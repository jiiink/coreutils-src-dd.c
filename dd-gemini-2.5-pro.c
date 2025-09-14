/* dd -- convert a file while copying it.
   Copyright (C) 1985-2025 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* Written by Paul Rubin, David MacKenzie, and Stuart Kemp. */

#include <config.h>

#include <ctype.h>
#include <sys/types.h>
#include <signal.h>

#include "system.h"
#include "alignalloc.h"
#include "close-stream.h"
#include "fd-reopen.h"
#include "gethrxtime.h"
#include "human.h"
#include "ioblksize.h"
#include "long-options.h"
#include "quote.h"
#include "xstrtol.h"
#include "xtime.h"

/* The official name of this program (e.g., no 'g' prefix).  */
#define PROGRAM_NAME "dd"

#define AUTHORS \
  proper_name ("Paul Rubin"), \
  proper_name ("David MacKenzie"), \
  proper_name ("Stuart Kemp")

/* Use SA_NOCLDSTOP as a proxy for whether the sigaction machinery is
   present.  */
#ifndef SA_NOCLDSTOP
# define SA_NOCLDSTOP 0
# define sigprocmask(How, Set, Oset) /* empty */
# define sigset_t int
# if ! HAVE_SIGINTERRUPT
#  define siginterrupt(sig, flag) /* empty */
# endif
#endif

/* NonStop circa 2011 lacks SA_RESETHAND; see Bug#9076.  */
#ifndef SA_RESETHAND
# define SA_RESETHAND 0
#endif

#ifndef SIGINFO
# define SIGINFO SIGUSR1
#endif

/* This may belong in GNULIB's fcntl module instead.
   Define O_CIO to 0 if it is not supported by this OS. */
#ifndef O_CIO
# define O_CIO 0
#endif

/* On AIX 5.1 and AIX 5.2, O_NOCACHE is defined via <fcntl.h>
   and would interfere with our use of that name, below.  */
#undef O_NOCACHE

#define output_char(c)				\
  do						\
    {						\
      obuf[oc++] = (c);				\
      if (oc >= output_blocksize)		\
        write_output ();			\
    }						\
  while (0)

/* Default input and output blocksize. */
#define DEFAULT_BLOCKSIZE 512

/* Conversions bit masks. */
enum
  {
    C_ASCII = 01,

    C_EBCDIC = 02,
    C_IBM = 04,
    C_BLOCK = 010,
    C_UNBLOCK = 020,
    C_LCASE = 040,
    C_UCASE = 0100,
    C_SWAB = 0200,
    C_NOERROR = 0400,
    C_NOTRUNC = 01000,
    C_SYNC = 02000,

    /* Use separate input and output buffers, and combine partial
       input blocks. */
    C_TWOBUFS = 04000,

    C_NOCREAT = 010000,
    C_EXCL = 020000,
    C_FDATASYNC = 040000,
    C_FSYNC = 0100000,

    C_SPARSE = 0200000
  };

/* Status levels.  */
enum
  {
    STATUS_NONE = 1,
    STATUS_NOXFER = 2,
    STATUS_DEFAULT = 3,
    STATUS_PROGRESS = 4
  };

/* The name of the input file, or nullptr for the standard input. */
static char const *input_file = nullptr;

/* The name of the output file, or nullptr for the standard output. */
static char const *output_file = nullptr;

/* The page size on this host.  */
static idx_t page_size;

/* The number of bytes in which atomic reads are done. */
static idx_t input_blocksize = 0;

/* The number of bytes in which atomic writes are done. */
static idx_t output_blocksize = 0;

/* Conversion buffer size, in bytes.  0 prevents conversions. */
static idx_t conversion_blocksize = 0;

/* Skip this many records of 'input_blocksize' bytes before input. */
static intmax_t skip_records = 0;

/* Skip this many bytes before input in addition of 'skip_records'
   records.  */
static idx_t skip_bytes = 0;

/* Skip this many records of 'output_blocksize' bytes before output. */
static intmax_t seek_records = 0;

/* Skip this many bytes in addition to 'seek_records' records before
   output.  */
static intmax_t seek_bytes = 0;

/* Whether the final output was done with a seek (rather than a write).  */
static bool final_op_was_seek;

/* Copy only this many records.  The default is effectively infinity.  */
static intmax_t max_records = INTMAX_MAX;

/* Copy this many bytes in addition to 'max_records' records.  */
static idx_t max_bytes = 0;

/* Bit vector of conversions to apply. */
static int conversions_mask = 0;

/* Open flags for the input and output files.  */
static int input_flags = 0;
static int output_flags = 0;

/* Status flags for what is printed to stderr.  */
static int status_level = STATUS_DEFAULT;

/* If nonzero, filter characters through the translation table.  */
static bool translation_needed = false;

/* Number of partial blocks written. */
static intmax_t w_partial = 0;

/* Number of full blocks written. */
static intmax_t w_full = 0;

/* Number of partial blocks read. */
static intmax_t r_partial = 0;

/* Number of full blocks read. */
static intmax_t r_full = 0;

/* Number of bytes written.  */
static intmax_t w_bytes = 0;

/* Last-reported number of bytes written, or negative if never reported.  */
static intmax_t reported_w_bytes = -1;

/* Time that dd started.  */
static xtime_t start_time;

/* Next time to report periodic progress.  */
static xtime_t next_time;

/* If positive, the number of bytes output in the current progress line.  */
static int progress_len;

/* True if input is seekable.  */
static bool input_seekable;

/* Error number corresponding to initial attempt to lseek input.
   If ESPIPE, do not issue any more diagnostics about it.  */
static int input_seek_errno;

/* File offset of the input, in bytes, or -1 if it overflowed.  */
static off_t input_offset;

/* True if a partial read should be diagnosed.  */
static bool warn_partial_read;

/* Records truncated by conv=block. */
static intmax_t r_truncate = 0;

/* Output representation of newline and space characters.
   They change if we're converting to EBCDIC.  */
static char newline_character = '\n';
static char space_character = ' ';

/* I/O buffers.  */
static char *ibuf;
static char *obuf;

/* Current index into 'obuf'. */
static idx_t oc = 0;

/* Index into current line, for 'conv=block' and 'conv=unblock'.  */
static idx_t col = 0;

/* The set of signals that are caught.  */
static sigset_t caught_signals;

/* If nonzero, the value of the pending fatal signal.  */
static sig_atomic_t volatile interrupt_signal;

/* A count of the number of pending info signals that have been received.  */
static sig_atomic_t volatile info_signal_count;

/* Whether to discard cache for input or output.  */
static bool i_nocache, o_nocache;

/* Whether to instruct the kernel to discard the complete file.  */
static bool i_nocache_eof, o_nocache_eof;

/* Function used for read (to handle iflag=fullblock parameter).  */
static ssize_t (*iread_fnc) (int fd, char *buf, idx_t size);

/* A longest symbol in the struct symbol_values tables below.  */
#define LONGEST_SYMBOL "count_bytes"

/* A symbol and the corresponding integer value.  */
struct symbol_value
{
  char symbol[sizeof LONGEST_SYMBOL];
  int value;
};

/* Conversion symbols, for conv="...".  */
static struct symbol_value const conversions[] =
{
  {"ascii", C_ASCII | C_UNBLOCK | C_TWOBUFS},	/* EBCDIC to ASCII. */
  {"ebcdic", C_EBCDIC | C_BLOCK | C_TWOBUFS},	/* ASCII to EBCDIC. */
  {"ibm", C_IBM | C_BLOCK | C_TWOBUFS},	/* Different ASCII to EBCDIC. */
  {"block", C_BLOCK | C_TWOBUFS},	/* Variable to fixed length records. */
  {"unblock", C_UNBLOCK | C_TWOBUFS},	/* Fixed to variable length records. */
  {"lcase", C_LCASE | C_TWOBUFS},	/* Translate upper to lower case. */
  {"ucase", C_UCASE | C_TWOBUFS},	/* Translate lower to upper case. */
  {"sparse", C_SPARSE},		/* Try to sparsely write output. */
  {"swab", C_SWAB | C_TWOBUFS},	/* Swap bytes of input. */
  {"noerror", C_NOERROR},	/* Ignore i/o errors. */
  {"nocreat", C_NOCREAT},	/* Do not create output file.  */
  {"excl", C_EXCL},		/* Fail if the output file already exists.  */
  {"notrunc", C_NOTRUNC},	/* Do not truncate output file. */
  {"sync", C_SYNC},		/* Pad input records to ibs with NULs. */
  {"fdatasync", C_FDATASYNC},	/* Synchronize output data before finishing.  */
  {"fsync", C_FSYNC},		/* Also synchronize output metadata.  */
  {"", 0}
};

#define FFS_MASK(x) ((x) ^ ((x) & ((x) - 1)))
enum
  {
    /* Compute a value that's bitwise disjoint from the union
       of all O_ values.  */
    v = ~(0
          | O_APPEND
          | O_BINARY
          | O_CIO
          | O_DIRECT
          | O_DIRECTORY
          | O_DSYNC
          | O_NOATIME
          | O_NOCTTY
          | O_NOFOLLOW
          | O_NOLINKS
          | O_NONBLOCK
          | O_SYNC
          | O_TEXT
          ),

    /* Use its lowest bits for private flags.  */
    O_FULLBLOCK = FFS_MASK (v),
    v2 = v ^ O_FULLBLOCK,

    O_NOCACHE = FFS_MASK (v2),
    v3 = v2 ^ O_NOCACHE,

    O_COUNT_BYTES = FFS_MASK (v3),
    v4 = v3 ^ O_COUNT_BYTES,

    O_SKIP_BYTES = FFS_MASK (v4),
    v5 = v4 ^ O_SKIP_BYTES,

    O_SEEK_BYTES = FFS_MASK (v5)
  };

/* Ensure that we got something.  */
static_assert (O_FULLBLOCK != 0);
static_assert (O_NOCACHE != 0);
static_assert (O_COUNT_BYTES != 0);
static_assert (O_SKIP_BYTES != 0);
static_assert (O_SEEK_BYTES != 0);

#define MULTIPLE_BITS_SET(i) (((i) & ((i) - 1)) != 0)

/* Ensure that this is a single-bit value.  */
static_assert ( ! MULTIPLE_BITS_SET (O_FULLBLOCK));
static_assert ( ! MULTIPLE_BITS_SET (O_NOCACHE));
static_assert ( ! MULTIPLE_BITS_SET (O_COUNT_BYTES));
static_assert ( ! MULTIPLE_BITS_SET (O_SKIP_BYTES));
static_assert ( ! MULTIPLE_BITS_SET (O_SEEK_BYTES));

/* Flags, for iflag="..." and oflag="...".  */
static struct symbol_value const flags[] =
{
  {"append",	  O_APPEND},
  {"binary",	  O_BINARY},
  {"cio",	  O_CIO},
  {"direct",	  O_DIRECT},
  {"directory",   O_DIRECTORY},
  {"dsync",	  O_DSYNC},
  {"noatime",	  O_NOATIME},
  {"nocache",	  O_NOCACHE},   /* Discard cache.  */
  {"noctty",	  O_NOCTTY},
  {"nofollow",	  HAVE_WORKING_O_NOFOLLOW ? O_NOFOLLOW : 0},
  {"nolinks",	  O_NOLINKS},
  {"nonblock",	  O_NONBLOCK},
  {"sync",	  O_SYNC},
  {"text",	  O_TEXT},
  {"fullblock",   O_FULLBLOCK}, /* Accumulate full blocks from input.  */
  {"count_bytes", O_COUNT_BYTES},
  {"skip_bytes",  O_SKIP_BYTES},
  {"seek_bytes",  O_SEEK_BYTES},
  {"",		0}
};

/* Status, for status="...".  */
static struct symbol_value const statuses[] =
{
  {"none",	STATUS_NONE},
  {"noxfer",	STATUS_NOXFER},
  {"progress",	STATUS_PROGRESS},
  {"",		0}
};

/* Translation table formed by applying successive transformations. */
static unsigned char trans_table[256];

/* Standard translation tables, taken from POSIX 1003.1-2013.
   Beware of imitations; there are lots of ASCII<->EBCDIC tables
   floating around the net, perhaps valid for some applications but
   not correct here.  */

static char const ascii_to_ebcdic[] =
{
  '\000', '\001', '\002', '\003', '\067', '\055', '\056', '\057',
  '\026', '\005', '\045', '\013', '\014', '\015', '\016', '\017',
  '\020', '\021', '\022', '\023', '\074', '\075', '\062', '\046',
  '\030', '\031', '\077', '\047', '\034', '\035', '\036', '\037',
  '\100', '\132', '\177', '\173', '\133', '\154', '\120', '\175',
  '\115', '\135', '\134', '\116', '\153', '\140', '\113', '\141',
  '\360', '\361', '\362', '\363', '\364', '\365', '\366', '\367',
  '\370', '\371', '\172', '\136', '\114', '\176', '\156', '\157',
  '\174', '\301', '\302', '\303', '\304', '\305', '\306', '\307',
  '\310', '\311', '\321', '\322', '\323', '\324', '\325', '\326',
  '\327', '\330', '\331', '\342', '\343', '\344', '\345', '\346',
  '\347', '\350', '\351', '\255', '\340', '\275', '\232', '\155',
  '\171', '\201', '\202', '\203', '\204', '\205', '\206', '\207',
  '\210', '\211', '\221', '\222', '\223', '\224', '\225', '\226',
  '\227', '\230', '\231', '\242', '\243', '\244', '\245', '\246',
  '\247', '\250', '\251', '\300', '\117', '\320', '\137', '\007',
  '\040', '\041', '\042', '\043', '\044', '\025', '\006', '\027',
  '\050', '\051', '\052', '\053', '\054', '\011', '\012', '\033',
  '\060', '\061', '\032', '\063', '\064', '\065', '\066', '\010',
  '\070', '\071', '\072', '\073', '\004', '\024', '\076', '\341',
  '\101', '\102', '\103', '\104', '\105', '\106', '\107', '\110',
  '\111', '\121', '\122', '\123', '\124', '\125', '\126', '\127',
  '\130', '\131', '\142', '\143', '\144', '\145', '\146', '\147',
  '\150', '\151', '\160', '\161', '\162', '\163', '\164', '\165',
  '\166', '\167', '\170', '\200', '\212', '\213', '\214', '\215',
  '\216', '\217', '\220', '\152', '\233', '\234', '\235', '\236',
  '\237', '\240', '\252', '\253', '\254', '\112', '\256', '\257',
  '\260', '\261', '\262', '\263', '\264', '\265', '\266', '\267',
  '\270', '\271', '\272', '\273', '\274', '\241', '\276', '\277',
  '\312', '\313', '\314', '\315', '\316', '\317', '\332', '\333',
  '\334', '\335', '\336', '\337', '\352', '\353', '\354', '\355',
  '\356', '\357', '\372', '\373', '\374', '\375', '\376', '\377'
};

static char const ascii_to_ibm[] =
{
  '\000', '\001', '\002', '\003', '\067', '\055', '\056', '\057',
  '\026', '\005', '\045', '\013', '\014', '\015', '\016', '\017',
  '\020', '\021', '\022', '\023', '\074', '\075', '\062', '\046',
  '\030', '\031', '\077', '\047', '\034', '\035', '\036', '\037',
  '\100', '\132', '\177', '\173', '\133', '\154', '\120', '\175',
  '\115', '\135', '\134', '\116', '\153', '\140', '\113', '\141',
  '\360', '\361', '\362', '\363', '\364', '\365', '\366', '\367',
  '\370', '\371', '\172', '\136', '\114', '\176', '\156', '\157',
  '\174', '\301', '\302', '\303', '\304', '\305', '\306', '\307',
  '\310', '\311', '\321', '\322', '\323', '\324', '\325', '\326',
  '\327', '\330', '\331', '\342', '\343', '\344', '\345', '\346',
  '\347', '\350', '\351', '\255', '\340', '\275', '\137', '\155',
  '\171', '\201', '\202', '\203', '\204', '\205', '\206', '\207',
  '\210', '\211', '\221', '\222', '\223', '\224', '\225', '\226',
  '\227', '\230', '\231', '\242', '\243', '\244', '\245', '\246',
  '\247', '\250', '\251', '\300', '\117', '\320', '\241', '\007',
  '\040', '\041', '\042', '\043', '\044', '\025', '\006', '\027',
  '\050', '\051', '\052', '\053', '\054', '\011', '\012', '\033',
  '\060', '\061', '\032', '\063', '\064', '\065', '\066', '\010',
  '\070', '\071', '\072', '\073', '\004', '\024', '\076', '\341',
  '\101', '\102', '\103', '\104', '\105', '\106', '\107', '\110',
  '\111', '\121', '\122', '\123', '\124', '\125', '\126', '\127',
  '\130', '\131', '\142', '\143', '\144', '\145', '\146', '\147',
  '\150', '\151', '\160', '\161', '\162', '\163', '\164', '\165',
  '\166', '\167', '\170', '\200', '\212', '\213', '\214', '\215',
  '\216', '\217', '\220', '\232', '\233', '\234', '\235', '\236',
  '\237', '\240', '\252', '\253', '\254', '\255', '\256', '\257',
  '\260', '\261', '\262', '\263', '\264', '\265', '\266', '\267',
  '\270', '\271', '\272', '\273', '\274', '\275', '\276', '\277',
  '\312', '\313', '\314', '\315', '\316', '\317', '\332', '\333',
  '\334', '\335', '\336', '\337', '\352', '\353', '\354', '\355',
  '\356', '\357', '\372', '\373', '\374', '\375', '\376', '\377'
};

static char const ebcdic_to_ascii[] =
{
  '\000', '\001', '\002', '\003', '\234', '\011', '\206', '\177',
  '\227', '\215', '\216', '\013', '\014', '\015', '\016', '\017',
  '\020', '\021', '\022', '\023', '\235', '\205', '\010', '\207',
  '\030', '\031', '\222', '\217', '\034', '\035', '\036', '\037',
  '\200', '\201', '\202', '\203', '\204', '\012', '\027', '\033',
  '\210', '\211', '\212', '\213', '\214', '\005', '\006', '\007',
  '\220', '\221', '\026', '\223', '\224', '\225', '\226', '\004',
  '\230', '\231', '\232', '\233', '\024', '\025', '\236', '\032',
  '\040', '\240', '\241', '\242', '\243', '\244', '\245', '\246',
  '\247', '\250', '\325', '\056', '\074', '\050', '\053', '\174',
  '\046', '\251', '\252', '\253', '\254', '\255', '\256', '\257',
  '\260', '\261', '\041', '\044', '\052', '\051', '\073', '\176',
  '\055', '\057', '\262', '\263', '\264', '\265', '\266', '\267',
  '\270', '\271', '\313', '\054', '\045', '\137', '\076', '\077',
  '\272', '\273', '\274', '\275', '\276', '\277', '\300', '\301',
  '\302', '\140', '\072', '\043', '\100', '\047', '\075', '\042',
  '\303', '\141', '\142', '\143', '\144', '\145', '\146', '\147',
  '\150', '\151', '\304', '\305', '\306', '\307', '\310', '\311',
  '\312', '\152', '\153', '\154', '\155', '\156', '\157', '\160',
  '\161', '\162', '\136', '\314', '\315', '\316', '\317', '\320',
  '\321', '\345', '\163', '\164', '\165', '\166', '\167', '\170',
  '\171', '\172', '\322', '\323', '\324', '\133', '\326', '\327',
  '\330', '\331', '\332', '\333', '\334', '\335', '\336', '\337',
  '\340', '\341', '\342', '\343', '\344', '\135', '\346', '\347',
  '\173', '\101', '\102', '\103', '\104', '\105', '\106', '\107',
  '\110', '\111', '\350', '\351', '\352', '\353', '\354', '\355',
  '\175', '\112', '\113', '\114', '\115', '\116', '\117', '\120',
  '\121', '\122', '\356', '\357', '\360', '\361', '\362', '\363',
  '\134', '\237', '\123', '\124', '\125', '\126', '\127', '\130',
  '\131', '\132', '\364', '\365', '\366', '\367', '\370', '\371',
  '\060', '\061', '\062', '\063', '\064', '\065', '\066', '\067',
  '\070', '\071', '\372', '\373', '\374', '\375', '\376', '\377'
};

/* True if we need to close the standard output *stream*.  */
static bool close_stdout_required = true;

/* The only reason to close the standard output *stream* is if
   parse_long_options fails (as it does for --help or --version).
   In any other case, dd uses only the STDOUT_FILENO file descriptor,
   and the "cleanup" function calls "close (STDOUT_FILENO)".
   Closing the file descriptor and then letting the usual atexit-run
   close_stdout function call "fclose (stdout)" would result in a
   harmless failure of the close syscall (with errno EBADF).
   This function serves solely to avoid the unnecessary close_stdout
   call, once parse_long_options has succeeded.
   Meanwhile, we guarantee that the standard error stream is flushed,
   by inlining the last half of close_stdout as needed.  */
static void
maybe_close_stdout (void)
{
  if (close_stdout_required)
    {
      close_stdout ();
    }
  else if (close_stream (stderr) != 0)
    {
      _exit (EXIT_FAILURE);
    }
}

/* Like the 'error' function but handle any pending newline,
   and do not exit.  */

ATTRIBUTE_FORMAT ((__printf__, 2, 3))
static void diagnose(int errnum, const char *fmt, ...)
{
    if (progress_len > 0)
    {
        fputc('\n', stderr);
        progress_len = 0;
    }

    va_list ap;
    va_start(ap, fmt);
    verror(0, errnum, fmt, ap);
    va_end(ap);
}

static void
print_usage_header (void)
{
  printf (_("Usage: %s [OPERAND]...\n"
            "  or:  %s OPTION\n"),
          program_name, program_name);
  fputs (_("Copy a file, converting and formatting according to the operands.\n\n"),
         stdout);
}

static void
print_operands (void)
{
  fputs (_("  bs=BYTES        read and write up to BYTES bytes at a time "
           "(default: 512);\n"
           "                  overrides ibs and obs\n"
           "  cbs=BYTES       convert BYTES bytes at a time\n"
           "  conv=CONVS      convert the file as per the comma separated "
           "symbol list\n"
           "  count=N         copy only N input blocks\n"
           "  ibs=BYTES       read up to BYTES bytes at a time (default: 512)\n"
           "  if=FILE         read from FILE instead of standard input\n"
           "  iflag=FLAGS     read as per the comma separated symbol list\n"
           "  obs=BYTES       write BYTES bytes at a time (default: 512)\n"
           "  of=FILE         write to FILE instead of standard output\n"
           "  oflag=FLAGS     write as per the comma separated symbol list\n"
           "  seek=N          (or oseek=N) skip N obs-sized output blocks\n"
           "  skip=N          (or iseek=N) skip N ibs-sized input blocks\n"
           "  status=LEVEL    The LEVEL of information to print to standard "
           "error;\n"
           "                  'none' suppresses everything but error messages,\n"
           "                  'noxfer' suppresses the final transfer "
           "statistics,\n"
           "                  'progress' shows periodic transfer statistics\n"),
         stdout);
}

static void
print_suffixes (void)
{
  fputs (_("\n"
           "N and BYTES may be followed by the following multiplicative suffixes:\n"
           "c=1, w=2, b=512, kB=1000, K=1024, MB=1000*1000, M=1024*1024, xM=M,\n"
           "GB=1000*1000*1000, G=1024*1024*1024, and so on for T, P, E, Z, Y, "
           "R, Q.\n"
           "Binary prefixes can be used, too: KiB=K, MiB=M, and so on.\n"
           "If N ends in 'B', it counts bytes not blocks.\n"),
         stdout);
}

static void
print_conv_symbols (void)
{
  fputs (_("\n"
           "Each CONV symbol may be:\n"
           "\n"
           "  ascii     from EBCDIC to ASCII\n"
           "  ebcdic    from ASCII to EBCDIC\n"
           "  ibm       from ASCII to alternate EBCDIC\n"
           "  block     pad newline-terminated records with spaces to "
           "cbs-size\n"
           "  unblock   replace trailing spaces in cbs-size records with "
           "newline\n"
           "  lcase     change upper case to lower case\n"
           "  ucase     change lower case to upper case\n"
           "  sparse    try to seek rather than write all-NUL output blocks\n"
           "  swab      swap every pair of input bytes\n"
           "  sync      pad every input block with NULs to ibs-size; when used\n"
           "            with block or unblock, pad with spaces rather than "
           "NULs\n"
           "  excl      fail if the output file already exists\n"
           "  nocreat   do not create the output file\n"
           "  notrunc   do not truncate the output file\n"
           "  noerror   continue after read errors\n"
           "  fdatasync  physically write output file data before finishing\n"
           "  fsync     likewise, but also write metadata\n"),
         stdout);
}

static void
print_flag_symbols (void)
{
  fputs (_("\n"
           "Each FLAG symbol may be:\n"
           "\n"
           "  append    append mode (makes sense only for output; "
           "conv=notrunc suggested)\n"),
         stdout);
  if (O_CIO)
    fputs (_("  cio       use concurrent I/O for data\n"), stdout);
  if (O_DIRECT)
    fputs (_("  direct    use direct I/O for data\n"), stdout);
  fputs (_("  directory  fail unless a directory\n"), stdout);
  if (O_DSYNC)
    fputs (_("  dsync     use synchronized I/O for data\n"), stdout);
  if (O_SYNC)
    fputs (_("  sync      likewise, but also for metadata\n"), stdout);
  fputs (_("  fullblock  accumulate full blocks of input (iflag only)\n"),
         stdout);
  if (O_NONBLOCK)
    fputs (_("  nonblock  use non-blocking I/O\n"), stdout);
  if (O_NOATIME)
    fputs (_("  noatime   do not update access time\n"), stdout);
#if HAVE_POSIX_FADVISE
  if (O_NOCACHE)
    fputs (
        _("  nocache   Request to drop cache.  See also oflag=sync\n"),
        stdout);
#endif
  if (O_NOCTTY)
    fputs (_("  noctty    do not assign controlling terminal from file\n"),
           stdout);
  if (HAVE_WORKING_O_NOFOLLOW)
    fputs (_("  nofollow  do not follow symlinks\n"), stdout);
  if (O_NOLINKS)
    fputs (_("  nolinks   fail if multiply-linked\n"), stdout);
  if (O_BINARY)
    fputs (_("  binary    use binary I/O for data\n"), stdout);
  if (O_TEXT)
    fputs (_("  text      use text I/O for data\n"), stdout);
}

static void
print_footer (void)
{
  printf (_("\n"
            "Sending a %s signal to a running 'dd' process makes it\n"
            "print I/O statistics to standard error and then resume copying.\n"
            "\n"
            "Options are:\n"
            "\n"),
          SIGINFO == SIGUSR1 ? "USR1" : "INFO");

  fputs (HELP_OPTION_DESCRIPTION, stdout);
  fputs (VERSION_OPTION_DESCRIPTION, stdout);
  emit_ancillary_info (PROGRAM_NAME);
}

void
usage (int status)
{
  if (status != EXIT_SUCCESS)
    {
      emit_try_help ();
    }
  else
    {
      print_usage_header ();
      print_operands ();
      print_suffixes ();
      print_conv_symbols ();
      print_flag_symbols ();
      print_footer ();
    }
  exit (status);
}

/* Common options to use when displaying sizes and rates.  */

enum { human_opts = (human_autoscale | human_round_to_nearest
                     | human_space_before_unit | human_SI | human_B) };

/* Ensure input buffer IBUF is allocated.  */

static void
alloc_ibuf (void)
{
  if (ibuf)
    {
      return;
    }

  size_t alloc_size = input_blocksize;
  if (conversions_mask & C_SWAB)
    {
      alloc_size++;
    }

  ibuf = alignalloc (page_size, alloc_size);
  if (!ibuf)
    {
      char hbuf[LONGEST_HUMAN_READABLE + 1];
      const char *size_str = human_readable (input_blocksize, hbuf,
                                             human_opts | human_base_1024, 1, 1);
      error (EXIT_FAILURE, 0,
             _("memory exhausted by input buffer of size %td bytes (%s)"),
             input_blocksize, size_str);
    }
}

/* Ensure output buffer OBUF is allocated/initialized.  */

static void
alloc_obuf (void)
{
  if (obuf)
    {
      return;
    }

  if (!(conversions_mask & C_TWOBUFS))
    {
      alloc_ibuf ();
      obuf = ibuf;
      return;
    }

  obuf = alignalloc (page_size, output_blocksize);
  if (!obuf)
    {
      char hbuf[LONGEST_HUMAN_READABLE + 1];
      const char *hstr = human_readable (output_blocksize, hbuf,
                                         human_opts | human_base_1024, 1, 1);
      error (EXIT_FAILURE, 0,
             _("memory exhausted by output buffer of size %td bytes (%s)"),
             output_blocksize, hstr);
    }
}

static void
translate_charset (char const *new_trans)
{
  if (!new_trans)
    {
      return;
    }

  const int charset_size = 256;
  for (int i = 0; i < charset_size; i++)
    {
      unsigned char old_val = (unsigned char)trans_table[i];
      trans_table[i] = new_trans[old_val];
    }
  translation_needed = true;
}

/* Return true if I has more than one bit set.  I must be nonnegative.  */

static inline bool
multiple_bits_set(int i)
{
    return (i != 0) && ((i & (i - 1)) != 0);
}

static bool
abbreviation_lacks_prefix (char const *message)
{
  size_t len = strlen (message);
  return len >= 2 && message[len - 2] == ' ';
}

/* Print transfer statistics.  */

static void
print_xfer_stats (xtime_t progress_time)
{
  xtime_t now = progress_time ? progress_time : gethrxtime ();
  static const char slash_s[] = "/s";
  char hbuf[3][LONGEST_HUMAN_READABLE + sizeof slash_s];
  double delta_s = 0.0;
  const char *bytes_per_second;

  const char *si = human_readable (w_bytes, hbuf[0], human_opts, 1, 1);
  const char *iec = human_readable (w_bytes, hbuf[1],
                                    human_opts | human_base_1024, 1, 1);

  char *bpsbuf = hbuf[2];
  const size_t bpsbufsize = sizeof hbuf[2];

  if (start_time < now)
    {
      const double xtime_precision_double = XTIME_PRECISION;
      xtime_t delta_xtime = now - start_time;
      delta_s = delta_xtime / xtime_precision_double;
      human_readable (w_bytes, bpsbuf, human_opts,
                      XTIME_PRECISION, delta_xtime);
      size_t len = strlen (bpsbuf);
      snprintf (bpsbuf + len, bpsbufsize - len, "%s", slash_s);
      bytes_per_second = bpsbuf;
    }
  else
    {
      snprintf (bpsbuf, bpsbufsize, "%s B/s", _("Infinity"));
      bytes_per_second = bpsbuf;
    }

  if (progress_time)
    fputc ('\r', stderr);

  char delta_s_buf[24];
  const char *time_format = progress_time ? "%.0f s" : "%g s";
  snprintf (delta_s_buf, sizeof delta_s_buf, time_format, delta_s);

  int stats_len;
  if (abbreviation_lacks_prefix (si))
    {
      const char *fmt = ngettext ("%jd byte copied, %s, %s",
                                  "%jd bytes copied, %s, %s",
                                  select_plural (w_bytes));
      stats_len = fprintf (stderr, fmt, w_bytes, delta_s_buf, bytes_per_second);
    }
  else if (abbreviation_lacks_prefix (iec))
    {
      stats_len = fprintf (stderr, _("%jd bytes (%s) copied, %s, %s"),
                           w_bytes, si, delta_s_buf, bytes_per_second);
    }
  else
    {
      stats_len = fprintf (stderr, _("%jd bytes (%s, %s) copied, %s, %s"),
                           w_bytes, si, iec, delta_s_buf, bytes_per_second);
    }

  if (progress_time)
    {
      if (stats_len >= 0 && stats_len < progress_len)
        fprintf (stderr, "%*s", progress_len - stats_len, "");
      progress_len = stats_len;
    }
  else
    {
      fputc ('\n', stderr);
    }

  reported_w_bytes = w_bytes;
}

static void
print_stats (void)
{
  if (status_level == STATUS_NONE)
    {
      return;
    }

  if (progress_len > 0)
    {
      fputc ('\n', stderr);
      progress_len = 0;
    }

  fprintf (stderr,
           _("%jd+%jd records in\n"
             "%jd+%jd records out\n"),
           r_full, r_partial, w_full, w_partial);

  if (r_truncate != 0)
    {
      fprintf (stderr,
               ngettext ("%jd truncated record\n",
                         "%jd truncated records\n",
                         select_plural (r_truncate)),
               r_truncate);
    }

  if (status_level != STATUS_NOXFER)
    {
      print_xfer_stats (0);
    }
}

/* An ordinary signal was received; arrange for the program to exit.  */

static void
interrupt_handler(int sig)
{
    interrupt_signal = sig;
}

/* An info signal was received; arrange for the program to print status.  */

static void
siginfo_handler (int sig)
{
  (void)sig;
  info_signal_count++;
}

/* Install the signal handlers.  */

static void
install_signal_handlers (void)
{
  const bool catch_siginfo = ! (SIGINFO == SIGUSR1 && getenv ("POSIXLY_CORRECT"));

#if SA_NOCLDSTOP

  struct sigaction act;
  struct sigaction old_act;

  if (sigaction (SIGINT, NULL, &old_act) == -1)
    {
      perror ("sigaction: query SIGINT");
      exit (EXIT_FAILURE);
    }
  const bool catch_sigint = (old_act.sa_handler != SIG_IGN);

  sigemptyset (&act.sa_mask);
  if (catch_siginfo)
    {
      sigaddset (&act.sa_mask, SIGINFO);
    }
  if (catch_sigint)
    {
      sigaddset (&act.sa_mask, SIGINT);
    }

  if (catch_siginfo)
    {
      act.sa_handler = siginfo_handler;
      act.sa_flags = 0;
      if (sigaction (SIGINFO, &act, NULL) == -1)
        {
          perror ("sigaction: set SIGINFO");
          exit (EXIT_FAILURE);
        }
    }

  if (catch_sigint)
    {
      act.sa_handler = interrupt_handler;
      act.sa_flags = SA_NODEFER | SA_RESETHAND;
      if (sigaction (SIGINT, &act, NULL) == -1)
        {
          perror ("sigaction: set SIGINT");
          exit (EXIT_FAILURE);
        }
    }

#else

  if (catch_siginfo)
    {
      if (signal (SIGINFO, siginfo_handler) == SIG_ERR)
        {
          perror ("signal: set SIGINFO");
          exit (EXIT_FAILURE);
        }
      siginterrupt (SIGINFO, 1);
    }

  if (signal (SIGINT, SIG_IGN) != SIG_IGN)
    {
      if (signal (SIGINT, interrupt_handler) == SIG_ERR)
        {
          perror ("signal: set SIGINT");
          exit (EXIT_FAILURE);
        }
      siginterrupt (SIGINT, 1);
    }
#endif
}

/* Close FD.  Return 0 if successful, -1 (setting errno) otherwise.
   If close fails with errno == EINTR, POSIX says the file descriptor
   is in an unspecified state, so keep trying to close FD but do not
   consider EBADF to be an error.  Do not process signals.  This all
   differs somewhat from functions like ifdatasync and ifsync.  */
static int
iclose (int fd)
{
  int result;
  do
    {
      result = close (fd);
    }
  while (result == -1 && errno == EINTR);

  return result;
}

static int synchronize_output (void);

static void
close_or_error (int fd, const char *filename)
{
  if (iclose (fd) != 0)
    error (EXIT_FAILURE, errno, _("closing file %s"), quoteaf (filename));
}

static void
cleanup (void)
{
  if (!interrupt_signal)
    {
      int sync_status = synchronize_output ();
      if (sync_status)
        exit (sync_status);
    }

  close_or_error (STDIN_FILENO, input_file);

  /* Don't remove this call to close, even though close_stdout
     closes standard output.  This close is necessary when cleanup
     is called as a consequence of signal handling.  */
  close_or_error (STDOUT_FILENO, output_file);
}

/* Process any pending signals.  If signals are caught, this function
   should be called periodically.  Ideally there should never be an
   unbounded amount of time when signals are not being processed.  */

static void
process_signals (void)
{
  while (interrupt_signal || info_signal_count > 0)
    {
      int interrupt;
      int infos;
      sigset_t oldset;

      if (sigprocmask (SIG_BLOCK, &caught_signals, &oldset) != 0)
        {
          perror ("sigprocmask: SIG_BLOCK");
          abort ();
        }

      interrupt = interrupt_signal;
      infos = info_signal_count;

      if (infos > 0)
        info_signal_count = infos - 1;

      if (sigprocmask (SIG_SETMASK, &oldset, NULL) != 0)
        {
          perror ("sigprocmask: SIG_SETMASK");
          abort ();
        }

      if (interrupt)
        cleanup ();

      print_stats ();

      if (interrupt)
        raise (interrupt);
    }
}

static void finish_up(void)
{
  /* Process signals first, so that cleanup is called at most once. */
  process_signals();
  cleanup();
  print_stats();
}

#include <stdlib.h>
#include <stdnoreturn.h>

void finish_up(void);

static noreturn void
quit(int code)
{
  finish_up();
  exit(code);
}

/* Return LEN rounded down to a multiple of IO_BUFSIZE
   (to minimize calls to the expensive posix_fadvise (,POSIX_FADV_DONTNEED),
   while storing the remainder internally per FD.
   Pass LEN == 0 to get the current remainder.  */

static off_t
cache_round (int fd, off_t len)
{
  static off_t i_pending, o_pending;
  off_t *pending = (fd == STDIN_FILENO ? &i_pending : &o_pending);

  if (len == 0)
    {
      return *pending;
    }

  intmax_t total_pending;
  if (ckd_add (&total_pending, *pending, len))
    {
      total_pending = INTMAX_MAX;
    }

  off_t remainder = total_pending % IO_BUFSIZE;
  *pending = remainder;

  return total_pending - remainder;
}

/* Discard the cache from the current offset of either
   STDIN_FILENO or STDOUT_FILENO.
   Return true on success.
   Return false on failure, with errno set.  */

static bool
invalidate_cache (int fd, off_t len)
{
#if HAVE_POSIX_FADVISE
  bool is_stdin = (fd == STDIN_FILENO);
  bool nocache_eof = is_stdin ? i_nocache_eof : o_nocache_eof;
  off_t clen = cache_round (fd, len);

  if ((len > 0 && clen == 0) || (len == 0 && !nocache_eof))
    return true;

  off_t current_offset;
  off_t pending = (len > 0) ? cache_round (fd, 0) : 0;

  if (is_stdin)
    {
      if (!input_seekable)
        {
          errno = ESPIPE;
          return false;
        }
      current_offset = input_offset;
    }
  else
    {
      static off_t output_offset = -2;

      if (output_offset == -2)
        output_offset = lseek (fd, 0, SEEK_CUR);

      current_offset = output_offset;

      if (current_offset != -1 && len > 0)
        output_offset += clen + pending;
    }

  if (current_offset < 0)
    return false;

  off_t advise_len = clen;
  off_t advise_offset = current_offset - clen - pending;

  if (len == 0 && clen > 0 && nocache_eof)
    {
      advise_len = 0;
    }

  if (advise_len == 0)
    advise_offset -= advise_offset % page_size;

  int adv_ret = posix_fadvise (fd, advise_offset, advise_len, POSIX_FADV_DONTNEED);
  if (adv_ret != 0)
    {
      errno = adv_ret;
      return false;
    }

  return true;

#else
  errno = ENOTSUP;
  return false;
#endif
}

/* Read from FD into the buffer BUF of size SIZE, processing any
   signals that arrive before bytes are read.  Return the number of
   bytes read if successful, -1 (setting errno) on failure.  */

static ssize_t
iread (int fd, char *buf, idx_t size, ssize_t *prev_nread_ptr)
{
  ssize_t nread;
  const bool prev_was_partial = (*prev_nread_ptr > 0 && (idx_t)*prev_nread_ptr < size);

  do
    {
      process_signals ();
      nread = read (fd, buf, size);

      if (nread == -1 && errno == EINVAL && (input_flags & O_DIRECT) && prev_was_partial)
        {
          errno = 0;
          nread = 0;
        }
    }
  while (nread < 0 && errno == EINTR);

  if (nread > 0 && (idx_t)nread < size)
    {
      process_signals ();
    }

  if (warn_partial_read && nread > 0 && prev_was_partial)
    {
      if (status_level != STATUS_NONE)
        {
          diagnose (0, ngettext (("warning: partial read (%td byte); "
                                  "suggest iflag=fullblock"),
                                 ("warning: partial read (%td bytes); "
                                  "suggest iflag=fullblock"),
                                 select_plural ((unsigned long)*prev_nread_ptr)),
                    *prev_nread_ptr);
        }
      warn_partial_read = false;
    }

  *prev_nread_ptr = nread;
  return nread;
}

/* Wrapper around iread function to accumulate full blocks.  */
static ssize_t
iread_fullblock(int fd, void *buffer, size_t size)
{
    size_t total_read = 0;
    while (total_read < size)
    {
        ssize_t bytes_read = iread(fd, (char *)buffer + total_read, size - total_read);

        if (bytes_read < 0)
        {
            return bytes_read;
        }

        if (bytes_read == 0)
        {
            break;
        }

        total_read += (size_t)bytes_read;
    }

    return (ssize_t)total_read;
}

/* Write to FD the buffer BUF of size SIZE, processing any signals
   that arrive.  Return the number of bytes written, setting errno if
   this is less than SIZE.  Keep trying if there are partial
   writes.  */

static void
prepare_final_write_if_odirect (void)
{
  int old_flags = fcntl (STDOUT_FILENO, F_GETFL);
  if (fcntl (STDOUT_FILENO, F_SETFL, old_flags & ~O_DIRECT) != 0)
    {
      if (status_level != STATUS_NONE)
        {
          diagnose (errno, _("failed to turn off O_DIRECT: %s"),
                    quotef (output_file));
        }
      return;
    }

  o_nocache_eof = true;
  invalidate_cache (STDOUT_FILENO, 0);
  conversions_mask |= C_FSYNC;
}

static idx_t
iwrite (int fd, char const *buf, idx_t size)
{
  if ((output_flags & O_DIRECT) && size < output_blocksize)
    {
      prepare_final_write_if_odirect ();
    }

  idx_t total_written = 0;
  while (total_written < size)
    {
      process_signals ();

      ssize_t nwritten;
      idx_t remaining = size - total_written;
      const char *current_buf = buf + total_written;
      final_op_was_seek = false;

      if ((conversions_mask & C_SPARSE) && is_nul (current_buf, remaining))
        {
          if (lseek (fd, (off_t) remaining, SEEK_CUR) < 0)
            {
              conversions_mask &= ~C_SPARSE;
              nwritten = write (fd, current_buf, (size_t) remaining);
            }
          else
            {
              final_op_was_seek = true;
              nwritten = remaining;
            }
        }
      else
        {
          nwritten = write (fd, current_buf, (size_t) remaining);
        }

      if (nwritten > 0)
        {
          total_written += nwritten;
        }
      else
        {
          if (nwritten == 0)
            {
              errno = ENOSPC;
              break;
            }
          if (errno != EINTR)
            {
              break;
            }
        }
    }

  if (o_nocache && total_written)
    {
      invalidate_cache (fd, total_written);
    }

  return total_written;
}

/* Write, then empty, the output buffer 'obuf'. */

static void
write_output (void)
{
  idx_t nwritten = iwrite (STDOUT_FILENO, obuf, output_blocksize);
  w_bytes += nwritten;

  if (nwritten != output_blocksize)
    {
      diagnose (errno, _("writing to %s"), quoteaf (output_file));
      if (nwritten != 0)
        {
          w_partial++;
        }
      quit (EXIT_FAILURE);
    }

  w_full++;
  oc = 0;
}

/* Restart on EINTR from fdatasync.  */

static int
ifdatasync (int fd)
{
  for (;;)
    {
      process_signals ();
      int ret = fdatasync (fd);
      if (ret >= 0 || errno != EINTR)
        {
          return ret;
        }
    }
}

/* Restart on EINTR from fd_reopen.  */

static int
ifd_reopen (int desired_fd, char const *file, int flag, mode_t mode)
{
  for (;;)
    {
      process_signals ();
      int ret = fd_reopen (desired_fd, file, flag, mode);
      if (ret >= 0 || errno != EINTR)
        {
          return ret;
        }
    }
}

/* Restart on EINTR from fstat.  */

static int
ifstat (int fd, struct stat *st)
{
  for (;;)
    {
      process_signals ();
      int ret = fstat (fd, st);
      if (ret >= 0 || errno != EINTR)
        {
          return ret;
        }
    }
}

/* Restart on EINTR from fsync.  */

static int
ifsync (int fd)
{
  int ret;

  for (;;)
    {
      process_signals ();
      ret = fsync (fd);

      if (ret == 0 || errno != EINTR)
        {
          break;
        }
    }

  return ret;
}

/* Restart on EINTR from ftruncate.  */

static int
iftruncate (int fd, off_t length)
{
  int ret;

  for (;;)
    {
      process_signals ();
      ret = ftruncate (fd, length);

      if (ret == 0 || errno != EINTR)
        {
          return ret;
        }
    }
}

/* Return true if STR is of the form "PATTERN" or "PATTERNDELIM...".  */

ATTRIBUTE_PURE
static bool
operand_matches (char const *str, char const *pattern, char delim)
{
  while (*pattern)
    if (*str++ != *pattern++)
      return false;
  return !*str || *str == delim;
}

/* Interpret one "conv=..." or similar operand STR according to the
   symbols in TABLE, returning the flags specified.  If the operand
   cannot be parsed, use ERROR_MSGID to generate a diagnostic.  */

static int
parse_symbols (char const *str, struct symbol_value const *table,
               bool exclusive, char const *error_msgid)
{
  int value = 0;

  while (true)
    {
      char const *comma = strchr (str, ',');
      struct symbol_value const *entry;

      for (entry = table; entry->symbol[0]; entry++)
        {
          if (operand_matches (str, entry->symbol, ',') && entry->value)
            break;
        }

      if (!entry->symbol[0])
        {
          idx_t slen = comma ? (idx_t) (comma - str) : strlen (str);
          diagnose (0, "%s: %s", _(error_msgid),
                    quotearg_n_style_mem (0, locale_quoting_style,
                                          str, slen));
          usage (EXIT_FAILURE);
        }

      value = exclusive ? entry->value : (value | entry->value);

      if (!comma)
        break;
      str = comma + 1;
    }

  return value;
}

/* Return the value of STR, interpreted as a non-negative decimal integer,
   optionally multiplied by various values.
   Set *INVALID to an appropriate error value and return INTMAX_MAX if
   it is an overflow, an indeterminate value if some other error occurred.  */

static intmax_t
parse_integer (char const *str, strtol_error *invalid)
{
  uintmax_t n;
  char *suffix;
  static char const suffixes[] = "bcEGkKMPQRTwYZ0";
  strtol_error e = xstrtoumax (str, &suffix, 10, &n, suffixes);

  if ((e & ~LONGINT_OVERFLOW) == LONGINT_INVALID_SUFFIX_CHAR)
    {
      if (*suffix == 'B' && str < suffix && suffix[-1] != 'B')
        {
          suffix++;
          if (!*suffix)
            {
              e &= ~LONGINT_INVALID_SUFFIX_CHAR;
            }
        }
      else if (*suffix == 'x')
        {
          strtol_error f = LONGINT_OK;
          intmax_t o = parse_integer (suffix + 1, &f);
          intmax_t result;

          if ((f & ~LONGINT_OVERFLOW) != LONGINT_OK)
            {
              *invalid = f;
              return 0;
            }

          bool overflow = ckd_mul (&result, n, o);
          if (overflow || (result != 0 && ((e | f) & LONGINT_OVERFLOW)))
            {
              *invalid = LONGINT_OVERFLOW;
              return INTMAX_MAX;
            }

          if (result == 0 && STRPREFIX (str, "0x"))
            {
              diagnose (0, _("warning: %s is a zero multiplier; "
                           "use %s if that is intended"),
                      quote_n (0, "0x"), quote_n (1, "00x"));
            }

          *invalid = LONGINT_OK;
          return result;
        }
    }

  if ((e & ~LONGINT_OVERFLOW) != LONGINT_OK)
    {
      *invalid = e;
      return 0;
    }

  if (n > INTMAX_MAX)
    {
      *invalid = LONGINT_OVERFLOW;
      return INTMAX_MAX;
    }

  *invalid = e;
  return (intmax_t) n;
}

/* OPERAND is of the form "X=...".  Return true if X is NAME.  */

ATTRIBUTE_PURE
static bool
operand_is (char const *operand, char const *name)
{
  return operand_matches (operand, name, '=');
}

static void
parse_and_validate_numeric (const char *val, intmax_t n_min, intmax_t n_max,
                            idx_t *dest)
{
  strtol_error invalid = LONGINT_OK;
  intmax_t n = parse_integer (val, &invalid);

  if (invalid != LONGINT_OK || n < n_min || n > n_max)
    error (EXIT_FAILURE, (invalid == LONGINT_OVERFLOW || n > n_max) ? EOVERFLOW : 0,
           "%s: %s", _("invalid number"), quoteaf (val));

  *dest = n;
}

static void
finalize_block_sizes (idx_t blocksize)
{
  if (blocksize)
    input_blocksize = output_blocksize = blocksize;
  else
    conversions_mask |= C_TWOBUFS;

  if (input_blocksize == 0)
    input_blocksize = DEFAULT_BLOCKSIZE;
  if (output_blocksize == 0)
    output_blocksize = DEFAULT_BLOCKSIZE;
  if (conversion_blocksize == 0)
    conversions_mask &= ~(C_BLOCK | C_UNBLOCK);
}

static void
validate_incompatible_options (void)
{
  if (output_flags & O_FULLBLOCK)
    {
      diagnose (0, "%s: %s", _("invalid output flag"), quote ("fullblock"));
      usage (EXIT_FAILURE);
    }

  if (multiple_bits_set (conversions_mask & (C_ASCII | C_EBCDIC | C_IBM)))
    error (EXIT_FAILURE, 0, _("cannot combine any two of {ascii,ebcdic,ibm}"));
  if (multiple_bits_set (conversions_mask & (C_BLOCK | C_UNBLOCK)))
    error (EXIT_FAILURE, 0, _("cannot combine block and unblock"));
  if (multiple_bits_set (conversions_mask & (C_LCASE | C_UCASE)))
    error (EXIT_FAILURE, 0, _("cannot combine lcase and ucase"));
  if (multiple_bits_set (conversions_mask & (C_EXCL | C_NOCREAT)))
    error (EXIT_FAILURE, 0, _("cannot combine excl and nocreat"));
  if (multiple_bits_set (input_flags & (O_DIRECT | O_NOCACHE))
      || multiple_bits_set (output_flags & (O_DIRECT | O_NOCACHE)))
    error (EXIT_FAILURE, 0, _("cannot combine direct and nocache"));
}

static void
setup_io_modes (void)
{
  if (input_flags & (O_DSYNC | O_SYNC))
    input_flags |= O_RSYNC;

  warn_partial_read =
    (! (conversions_mask & C_TWOBUFS) && ! (input_flags & O_FULLBLOCK)
     && (skip_records
         || (0 < max_records && max_records < INTMAX_MAX)
         || (input_flags | output_flags) & O_DIRECT));

  iread_fnc = ((input_flags & O_FULLBLOCK)
               ? iread_fullblock
               : iread);
  input_flags &= ~O_FULLBLOCK;

  if (input_flags & O_NOCACHE)
    {
      i_nocache = true;
      i_nocache_eof = (max_records == 0 && max_bytes == 0);
      input_flags &= ~O_NOCACHE;
    }
  if (output_flags & O_NOCACHE)
    {
      o_nocache = true;
      o_nocache_eof = (max_records == 0 && max_bytes == 0);
      output_flags &= ~O_NOCACHE;
    }
}

static void
scanargs (int argc, char *const *argv)
{
  idx_t blocksize = 0;
  intmax_t count = INTMAX_MAX;
  intmax_t skip = 0;
  intmax_t seek = 0;
  bool count_B = false, skip_B = false, seek_B = false;

  idx_t max_blocksize = MIN (IDX_MAX - 1, MIN (SSIZE_MAX, OFF_T_MAX));

  for (int i = optind; i < argc; i++)
    {
      char const *name = argv[i];
      char const *val = strchr (name, '=');

      if (val == nullptr)
        {
          diagnose (0, _("unrecognized operand %s"), quoteaf (name));
          usage (EXIT_FAILURE);
        }
      val++;

      if (operand_is (name, "if"))
        input_file = val;
      else if (operand_is (name, "of"))
        output_file = val;
      else if (operand_is (name, "conv"))
        conversions_mask |= parse_symbols (val, conversions, false,
                                           N_("invalid conversion"));
      else if (operand_is (name, "iflag"))
        input_flags |= parse_symbols (val, flags, false,
                                      N_("invalid input flag"));
      else if (operand_is (name, "oflag"))
        output_flags |= parse_symbols (val, flags, false,
                                       N_("invalid output flag"));
      else if (operand_is (name, "status"))
        status_level = parse_symbols (val, statuses, true,
                                      N_("invalid status level"));
      else if (operand_is (name, "ibs"))
        parse_and_validate_numeric (val, 1, max_blocksize, &input_blocksize);
      else if (operand_is (name, "obs"))
        parse_and_validate_numeric (val, 1, max_blocksize, &output_blocksize);
      else if (operand_is (name, "bs"))
        parse_and_validate_numeric (val, 1, max_blocksize, &blocksize);
      else if (operand_is (name, "cbs"))
        parse_and_validate_numeric (val, 1, MIN (SIZE_MAX, IDX_MAX),
                                    &conversion_blocksize);
      else
        {
          strtol_error invalid = LONGINT_OK;
          intmax_t n = parse_integer (val, &invalid);

          if (invalid != LONGINT_OK || n < 0)
            error (EXIT_FAILURE, invalid == LONGINT_OVERFLOW ? EOVERFLOW : 0,
                   "%s: %s", _("invalid number"), quoteaf (val));

          bool has_B = !!strchr (val, 'B');

          if (operand_is (name, "skip") || operand_is (name, "iseek"))
            {
              skip = n;
              skip_B = has_B;
            }
          else if (operand_is (name + (*name == 'o'), "seek"))
            {
              seek = n;
              seek_B = has_B;
            }
          else if (operand_is (name, "count"))
            {
              count = n;
              count_B = has_B;
            }
          else
            {
              diagnose (0, _("unrecognized operand %s"), quoteaf (name));
              usage (EXIT_FAILURE);
            }
        }
    }

  finalize_block_sizes (blocksize);

  if (skip_B)
    input_flags |= O_SKIP_BYTES;
  if (skip != 0)
    {
      if (input_flags & O_SKIP_BYTES)
        {
          skip_records = skip / input_blocksize;
          skip_bytes = skip % input_blocksize;
        }
      else
        skip_records = skip;
    }

  if (count_B)
    input_flags |= O_COUNT_BYTES;
  if (count != INTMAX_MAX)
    {
      if (input_flags & O_COUNT_BYTES)
        {
          max_records = count / input_blocksize;
          max_bytes = count % input_blocksize;
        }
      else
        max_records = count;
    }

  if (seek_B)
    output_flags |= O_SEEK_BYTES;
  if (seek != 0)
    {
      if (output_flags & O_SEEK_BYTES)
        {
          seek_records = seek / output_blocksize;
          seek_bytes = seek % output_blocksize;
        }
      else
        seek_records = seek;
    }

  validate_incompatible_options ();
  setup_io_modes ();
}

/* Fix up translation table. */

#define CHARSET_SIZE 256

static void
apply_translations (void)
{
  if (conversions_mask & C_ASCII)
    translate_charset (ebcdic_to_ascii);

  int (*case_func) (int) = 0;
  if (conversions_mask & C_UCASE)
    case_func = toupper;
  else if (conversions_mask & C_LCASE)
    case_func = tolower;

  if (case_func)
    {
      for (int i = 0; i < CHARSET_SIZE; i++)
        trans_table[i] =
          (unsigned char) case_func ((unsigned char) trans_table[i]);
      translation_needed = true;
    }

  const unsigned char *target_map = 0;
  if (conversions_mask & C_EBCDIC)
    target_map = ascii_to_ebcdic;
  else if (conversions_mask & C_IBM)
    target_map = ascii_to_ibm;

  if (target_map)
    {
      translate_charset (target_map);
      newline_character = target_map[(unsigned char) '\n'];
      space_character = target_map[(unsigned char) ' '];
    }
}

/* Apply the character-set translations specified by the user
   to the NREAD bytes in BUF.  */

static void
translate_buffer (char *buf, idx_t nread)
{
  if (!buf)
    {
      return;
    }

  for (idx_t i = 0; i < nread; ++i)
    {
      buf[i] = trans_table[(unsigned char) buf[i]];
    }
}

/* Swap *NREAD bytes in BUF, which should have room for an extra byte
   after the end because the swapping is not in-place.  If *SAVED_BYTE
   is nonnegative, also swap that initial byte from the previous call.
   Save the last byte into into *SAVED_BYTE if needed to make the
   resulting *NREAD even, and set *SAVED_BYTE to -1 otherwise.
   Return the buffer's adjusted start, either BUF or BUF + 1.  */

static char *
swab_buffer (char *buf, idx_t *nread, int *saved_byte)
{
  if (*nread == 0)
    {
      return buf;
    }

  int prev_saved = *saved_byte;
  char *result_buf = buf;

  if (((prev_saved >= 0) + *nread) & 1)
    {
      *saved_byte = (unsigned char) buf[--*nread];
    }
  else
    {
      *saved_byte = -1;
    }

  if (prev_saved >= 0)
    {
      memmove (buf + 1, buf, *nread);
      buf[0] = (char) prev_saved;
      *nread += 1;
    }

  for (idx_t i = 0; i < *nread; i += 2)
    {
      char temp = buf[i];
      buf[i] = buf[i + 1];
      buf[i + 1] = temp;
    }

  if (prev_saved < 0)
    {
      memmove (buf + 1, buf, *nread);
      result_buf = buf + 1;
    }

  return result_buf;
}

/* Add OFFSET to the input offset, setting the overflow flag if
   necessary.  */

static void
advance_input_offset (intmax_t offset)
{
  if (input_offset < 0)
    return;

  intmax_t new_offset;
  if (ckd_add (&new_offset, input_offset, offset))
    input_offset = -1;
  else
    input_offset = new_offset;
}

/* Throw away RECORDS blocks of BLOCKSIZE bytes plus BYTES bytes on
   file descriptor FDESC, which is open with read permission for FILE.
   Store up to BLOCKSIZE bytes of the data at a time in IBUF or OBUF, if
   necessary. RECORDS or BYTES must be nonzero. If FDESC is
   STDIN_FILENO, advance the input offset. Return the number of
   records remaining, i.e., that were not skipped because EOF was
   reached.  If FDESC is STDOUT_FILENO, on return, BYTES is the
   remaining bytes in addition to the remaining records.  */

static intmax_t
handle_stdin_lseek_success (char const *file, off_t offset,
                            intmax_t records, idx_t blocksize)
{
  struct stat st;
  if (ifstat (STDIN_FILENO, &st) != 0)
    error (EXIT_FAILURE, errno, _("cannot fstat %s"), quoteaf (file));

  if (usable_st_size (&st) && 0 < st.st_size && 0 <= input_offset
      && st.st_size - input_offset < offset)
    {
      /* When skipping past EOF, return the number of _full_ blocks
       * that are not skipped, and set offset to EOF, so the caller
       * can determine the requested skip was not satisfied.  */
      records = (offset - st.st_size) / blocksize;
      offset = st.st_size - input_offset;
    }
  else
    {
      records = 0;
    }

  advance_input_offset (offset);
  return records;
}

static intmax_t
skip_by_reading (int fdesc, char const *file, intmax_t records,
                 idx_t blocksize, idx_t *bytes, int lseek_errno)
{
  /* The seek request may have failed above
     (> device size, > max file size, etc.)
     Or it may not have been done at all (> OFF_T_MAX).
     Therefore try to seek to the end of the file,
     to avoid redundant reading.  */
  if (lseek (fdesc, 0, SEEK_END) >= 0)
    {
      /* File is seekable, and we're at the end of it, and
         size <= OFF_T_MAX. So there's no point using read to advance. */
      if (!lseek_errno)
        {
          /* The original seek was not attempted as offset > OFF_T_MAX.
             We should error for write as can't get to the desired
             location, even if OFF_T_MAX < max file size.
             For read we're not going to read any data anyway,
             so we should error for consistency.
             It would be nice to not error for /dev/{zero,null}
             for any offset, but that's not a significant issue.  */
          lseek_errno = EOVERFLOW;
        }

      diagnose (lseek_errno,
                gettext (fdesc == STDIN_FILENO
                         ? N_("%s: cannot skip")
                         : N_("%s: cannot seek")),
                quotef (file));
      quit (EXIT_FAILURE);
    }
  /* else file_size && offset > OFF_T_MAX or file ! seekable */

  char *buf;
  if (fdesc == STDIN_FILENO)
    {
      alloc_ibuf ();
      buf = ibuf;
    }
  else
    {
      alloc_obuf ();
      buf = obuf;
    }

  while (records || *bytes)
    {
      ssize_t nread = iread_fnc (fdesc, buf, records ? blocksize : *bytes);
      if (nread < 0)
        {
          if (fdesc == STDIN_FILENO)
            {
              diagnose (errno, _("error reading %s"), quoteaf (file));
              if (conversions_mask & C_NOERROR)
                print_stats ();
            }
          else
            {
              diagnose (lseek_errno, _("%s: cannot seek"), quotef (file));
            }
          quit (EXIT_FAILURE);
        }
      if (nread == 0)
        break;
      if (fdesc == STDIN_FILENO)
        advance_input_offset (nread);

      if (records)
        records--;
      else
        *bytes = 0;
    }

  return records;
}

static intmax_t
skip (int fdesc, char const *file, intmax_t records, idx_t blocksize,
      idx_t *bytes)
{
  /* Try lseek and if an error indicates it was an inappropriate operation --
     or if the file offset is not representable as an off_t --
     fall back on using read.  */
  errno = 0;
  off_t offset;
  if (! ckd_mul (&offset, records, blocksize)
      && ! ckd_add (&offset, offset, *bytes)
      && 0 <= lseek (fdesc, offset, SEEK_CUR))
    {
      if (fdesc == STDIN_FILENO)
        return handle_stdin_lseek_success (file, offset, records, blocksize);

      records = 0;
      *bytes = 0;
      return records;
    }

  return skip_by_reading (fdesc, file, records, blocksize, bytes, errno);
}

/* Advance the input by NBYTES if possible, after a read error.
   The input file offset may or may not have advanced after the failed
   read; adjust it to point just after the bad record regardless.
   Return true if successful, or if the input is already known to not
   be seekable.  */

static bool
advance_input_after_read_error (idx_t nbytes)
{
  if (!input_seekable)
    {
      if (input_seek_errno == ESPIPE)
        return true;
      errno = input_seek_errno;
      diagnose (errno, _("%s: cannot seek"), quotef (input_file));
      return false;
    }

  advance_input_offset (nbytes);
  if (input_offset < 0)
    {
      diagnose (0, _("offset overflow while reading file %s"),
                quoteaf (input_file));
      return false;
    }

  off_t offset = lseek (STDIN_FILENO, 0, SEEK_CUR);
  if (offset < 0)
    {
      diagnose (errno, _("%s: cannot seek"), quotef (input_file));
      return false;
    }

  if (offset == input_offset)
    return true;

  off_t diff = input_offset - offset;
  if (! (0 <= diff && diff <= nbytes) && status_level != STATUS_NONE)
    diagnose (0, _("warning: invalid file offset after failed read"));

  if (lseek (STDIN_FILENO, diff, SEEK_CUR) >= 0)
    return true;

  if (errno == 0)
    diagnose (0, _("cannot work around kernel bug after all"));

  diagnose (errno, _("%s: cannot seek"), quotef (input_file));
  return false;
}

/* Copy NREAD bytes of BUF, with no conversions.  */

static void
copy_simple (char const *buf, idx_t nread)
{
  while (nread > 0)
    {
      idx_t bytes_to_copy = MIN (nread, output_blocksize - oc);

      memcpy (obuf + oc, buf, bytes_to_copy);

      buf += bytes_to_copy;
      nread -= bytes_to_copy;
      oc += bytes_to_copy;

      if (oc == output_blocksize)
        write_output ();
    }
}

/* Copy NREAD bytes of BUF, doing conv=block
   (pad newline-terminated records to 'conversion_blocksize',
   replacing the newline with trailing spaces).  */

static void
copy_with_block (char const *buf, idx_t nread)
{
  for (idx_t i = 0; i < nread; i++)
    {
      const char current_char = buf[i];
      if (current_char == newline_character)
        {
          for (idx_t j = col; j < conversion_blocksize; j++)
            {
              output_char (space_character);
            }
          col = 0;
        }
      else
        {
          if (col < conversion_blocksize)
            {
              output_char (current_char);
            }
          else if (col == conversion_blocksize)
            {
              r_truncate++;
            }
          col++;
        }
    }
}

/* Copy NREAD bytes of BUF, doing conv=unblock
   (replace trailing spaces in 'conversion_blocksize'-sized records
   with a newline).  */

static void
copy_with_unblock (char const *buf, idx_t nread, idx_t *col,
                   idx_t *pending_spaces)
{
  idx_t i = 0;
  while (i < nread)
    {
      if (*col >= conversion_blocksize)
        {
          output_char (newline_character);
          *col = 0;
          *pending_spaces = 0;
        }
      else
        {
          char c = buf[i];
          if (c == space_character)
            {
              (*pending_spaces)++;
            }
          else
            {
              while (*pending_spaces > 0)
                {
                  output_char (space_character);
                  (*pending_spaces)--;
                }
              output_char (c);
            }
          (*col)++;
          i++;
        }
    }
}

/* Set the file descriptor flags for FD that correspond to the nonzero bits
   in ADD_FLAGS.  The file's name is NAME.  */

static void
set_fd_flags (int fd, int add_flags, char const *name)
{
  add_flags &= ~(O_NOCTTY | O_NOFOLLOW);

  if (!add_flags)
    return;

  int old_flags = fcntl (fd, F_GETFL);
  if (old_flags < 0)
    goto fail;

  int new_flags = old_flags | add_flags;

  if (old_flags == new_flags)
    return;

  if (new_flags & (O_DIRECTORY | O_NOLINKS))
    {
      struct stat st;
      if (fstat (fd, &st) != 0)
        goto fail;

      if ((new_flags & O_DIRECTORY) && !S_ISDIR (st.st_mode))
        {
          errno = ENOTDIR;
          goto fail;
        }

      if ((new_flags & O_NOLINKS) && 1 < st.st_nlink)
        {
          errno = EMLINK;
          goto fail;
        }

      new_flags &= ~(O_DIRECTORY | O_NOLINKS);
    }

  if (old_flags == new_flags)
    return;

  if (fcntl (fd, F_SETFL, new_flags) == -1)
    goto fail;

  return;

fail:
  error (EXIT_FAILURE, errno, _("setting flags for %s"), quoteaf (name));
}

/* The main loop.  */

typedef enum
{
  READ_SUCCESS,
  READ_EOF,
  READ_ERROR_RECOVER,
  READ_ERROR_FATAL
} read_status_t;

typedef struct
{
  read_status_t status;
  ssize_t nread;
} read_result_t;

static void
handle_skip_input (void)
{
  if (skip_records == 0 && skip_bytes == 0)
    return;

  intmax_t us_bytes;
  bool us_bytes_overflow =
    (ckd_mul (&us_bytes, skip_records, input_blocksize)
     || ckd_add (&us_bytes, skip_bytes, us_bytes));
  off_t input_offset0 = input_offset;
  intmax_t us_blocks = skip (STDIN_FILENO, input_file,
                             skip_records, input_blocksize, &skip_bytes);

  if ((us_blocks
       || (0 <= input_offset
           && (us_bytes_overflow
               || us_bytes != input_offset - input_offset0)))
      && status_level != STATUS_NONE)
    {
      diagnose (0, _("%s: cannot skip to specified offset"),
                quotef (input_file));
    }
}

static int
handle_seek_output (void)
{
  if (seek_records == 0 && seek_bytes == 0)
    return EXIT_SUCCESS;

  idx_t bytes = seek_bytes;
  intmax_t write_records = skip (STDOUT_FILENO, output_file,
                                 seek_records, output_blocksize, &bytes);

  if (write_records != 0 || bytes != 0)
    {
      memset (obuf, 0, write_records ? output_blocksize : bytes);

      do
        {
          idx_t size = write_records ? output_blocksize : bytes;
          if (iwrite (STDOUT_FILENO, obuf, size) != size)
            {
              diagnose (errno, _("writing to %s"), quoteaf (output_file));
              return EXIT_FAILURE;
            }

          if (write_records != 0)
            write_records--;
          else
            bytes = 0;
        }
      while (write_records || bytes);
    }
  return EXIT_SUCCESS;
}

static void
update_progress_report_if_needed (void)
{
  if (status_level == STATUS_PROGRESS)
    {
      xtime_t progress_time = gethrxtime ();
      if (next_time <= progress_time)
        {
          print_xfer_stats (progress_time);
          next_time += XTIME_PRECISION;
        }
    }
}

static read_result_t
read_input_block (idx_t partread, int *exit_status_ptr)
{
  read_result_t result = { READ_SUCCESS, 0 };

  if ((conversions_mask & C_SYNC) && (conversions_mask & C_NOERROR))
    memset (ibuf, (conversions_mask & (C_BLOCK | C_UNBLOCK)) ? ' ' : '\0',
            input_blocksize);

  idx_t read_size = (r_partial + r_full >= max_records)
                    ? max_bytes : input_blocksize;
  result.nread = iread_fnc (STDIN_FILENO, ibuf, read_size);

  if (result.nread > 0)
    {
      advance_input_offset (result.nread);
      if (i_nocache)
        invalidate_cache (STDIN_FILENO, result.nread);
    }
  else if (result.nread == 0)
    {
      i_nocache_eof |= i_nocache;
      o_nocache_eof |= o_nocache && ! (conversions_mask & C_NOTRUNC);
      result.status = READ_EOF;
    }
  else
    {
      if (!(conversions_mask & C_NOERROR) || status_level != STATUS_NONE)
        diagnose (errno, _("error reading %s"), quoteaf (input_file));

      if (conversions_mask & C_NOERROR)
        {
          idx_t bad_portion = input_blocksize - partread;
          invalidate_cache (STDIN_FILENO, bad_portion);
          if (!advance_input_after_read_error (bad_portion))
            {
              *exit_status_ptr = EXIT_FAILURE;
              input_seekable = false;
              input_seek_errno = ESPIPE;
            }
          if ((conversions_mask & C_SYNC) && !partread)
            result.nread = 0;
          else
            result.status = READ_ERROR_RECOVER;
        }
      else
        {
          *exit_status_ptr = EXIT_FAILURE;
          result.status = READ_ERROR_FATAL;
        }
    }
  return result;
}

static idx_t
prepare_input_buffer (ssize_t nread, idx_t *partread_ptr)
{
  idx_t n_bytes_to_process = nread;

  if (n_bytes_to_process < input_blocksize)
    {
      r_partial++;
      *partread_ptr = n_bytes_to_process;
      if (conversions_mask & C_SYNC)
        {
          if (!(conversions_mask & C_NOERROR))
            memset (ibuf + n_bytes_to_process,
                    (conversions_mask & (C_BLOCK | C_UNBLOCK)) ? ' ' : '\0',
                    input_blocksize - n_bytes_to_process);
          n_bytes_to_process = input_blocksize;
        }
    }
  else
    {
      r_full++;
      *partread_ptr = 0;
    }
  return n_bytes_to_process;
}

static int
process_simple_write (idx_t n_bytes)
{
  idx_t nwritten = iwrite (STDOUT_FILENO, obuf, n_bytes);
  w_bytes += nwritten;
  if (nwritten != n_bytes)
    {
      diagnose (errno, _("error writing %s"), quoteaf (output_file));
      return EXIT_FAILURE;
    }
  if (n_bytes == input_blocksize)
    w_full++;
  else
    w_partial++;
  return EXIT_SUCCESS;
}

static void
dispatch_copy (const char *buf, idx_t n_bytes)
{
  if (conversions_mask & C_BLOCK)
    copy_with_block (buf, n_bytes);
  else if (conversions_mask & C_UNBLOCK)
    copy_with_unblock (buf, n_bytes);
  else
    copy_simple (buf, n_bytes);
}

static int
truncate_output_file_if_needed (void)
{
  struct stat stdout_stat;
  if (ifstat (STDOUT_FILENO, &stdout_stat) != 0)
    {
      diagnose (errno, _("cannot fstat %s"), quoteaf (output_file));
      return EXIT_FAILURE;
    }

  if (S_ISREG (stdout_stat.st_mode) || S_TYPEISSHM (&stdout_stat))
    {
      off_t output_offset = lseek (STDOUT_FILENO, 0, SEEK_CUR);
      if (output_offset >= 0 && stdout_stat.st_size < output_offset)
        {
          if (iftruncate (STDOUT_FILENO, output_offset) != 0)
            {
              diagnose (errno, _("failed to truncate to %jd bytes"
                                 " in output file %s"),
                        (intmax_t) output_offset, quoteaf (output_file));
              return EXIT_FAILURE;
            }
        }
    }
  return EXIT_SUCCESS;
}

static int
finalize_copy (int saved_byte)
{
  if (saved_byte >= 0)
    {
      char saved_char = saved_byte;
      dispatch_copy (&saved_char, 1);
    }

  if ((conversions_mask & C_BLOCK) && col > 0)
    for (idx_t i = col; i < conversion_blocksize; i++)
      output_char (space_character);

  if (col > 0 && (conversions_mask & C_UNBLOCK))
    output_char (newline_character);

  if (oc > 0)
    {
      idx_t nwritten = iwrite (STDOUT_FILENO, obuf, oc);
      w_bytes += nwritten;
      if (nwritten > 0)
        w_partial++;
      if (nwritten != oc)
        {
          diagnose (errno, _("error writing %s"), quoteaf (output_file));
          return EXIT_FAILURE;
        }
    }

  if (final_op_was_seek)
    if (truncate_output_file_if_needed () != EXIT_SUCCESS)
      return EXIT_FAILURE;

  if (conversions_mask & (C_FDATASYNC | C_FSYNC)
      && status_level == STATUS_PROGRESS
      && 0 <= reported_w_bytes && reported_w_bytes < w_bytes)
    print_xfer_stats (0);

  return EXIT_SUCCESS;
}

static int
dd_copy (void)
{
  int exit_status = EXIT_SUCCESS;
  idx_t partread = 0;
  int saved_byte = -1;

  handle_skip_input ();
  if (handle_seek_output () != EXIT_SUCCESS)
    quit (EXIT_FAILURE);

  if (max_records == 0 && max_bytes == 0)
    return exit_status;

  alloc_ibuf ();
  alloc_obuf ();

  while (true)
    {
      update_progress_report_if_needed ();

      if (r_partial + r_full >= max_records + !!max_bytes)
        break;

      read_result_t res = read_input_block (partread, &exit_status);
      if (res.status == READ_EOF || res.status == READ_ERROR_FATAL)
        break;
      if (res.status == READ_ERROR_RECOVER)
        continue;

      idx_t n_bytes_to_process = prepare_input_buffer (res.nread, &partread);

      if (ibuf == obuf)
        {
          if (process_simple_write (n_bytes_to_process) != EXIT_SUCCESS)
            return EXIT_FAILURE;
          continue;
        }

      if (translation_needed)
        translate_buffer (ibuf, n_bytes_to_process);

      char *bufstart;
      idx_t converted_bytes = n_bytes_to_process;
      if (conversions_mask & C_SWAB)
        bufstart = swab_buffer (ibuf, &converted_bytes, &saved_byte);
      else
        bufstart = ibuf;

      dispatch_copy (bufstart, converted_bytes);
    }

  int finalize_status = finalize_copy (saved_byte);
  return (finalize_status == EXIT_FAILURE) ? EXIT_FAILURE : exit_status;
}

/* Synchronize output according to conversions_mask.
   Do this even if w_bytes is zero, as fsync and fdatasync
   flush out write requests from other processes too.
   Clear bits in conversions_mask so that synchronization is done only once.
   Return zero if successful, an exit status otherwise.  */

static int
synchronize_output (void)
{
  int const original_mask = conversions_mask;
  conversions_mask &= ~(C_FDATASYNC | C_FSYNC);

  int exit_status = 0;
  int needs_fsync = (original_mask & C_FSYNC);

  if ((original_mask & C_FDATASYNC) && ifdatasync (STDOUT_FILENO) != 0)
    {
      needs_fsync = 1;
      if (errno != ENOSYS && errno != EINVAL)
        {
          diagnose (errno, _("fdatasync failed for %s"), quoteaf (output_file));
          exit_status = EXIT_FAILURE;
        }
    }

  if (needs_fsync && ifsync (STDOUT_FILENO) != 0)
    {
      diagnose (errno, _("fsync failed for %s"), quoteaf (output_file));
      return EXIT_FAILURE;
    }

  return exit_status;
}

static void
initialize_program (int *argc, char ***argv)
{
  install_signal_handlers ();
  initialize_main (argc, argv);
  set_program_name ((*argv)[0]);
  setlocale (LC_ALL, "");
  bindtextdomain (PACKAGE, LOCALEDIR);
  textdomain (PACKAGE);

  atexit (maybe_close_stdout);

  page_size = getpagesize ();

  parse_gnu_standard_options_only (*argc, *argv, PROGRAM_NAME, PACKAGE, Version,
                                   true, usage, AUTHORS,
                                   (char const *) nullptr);
  close_stdout_required = false;

  for (int i = 0; i < 256; i++)
    trans_table[i] = i;

  scanargs (*argc, *argv);
  apply_translations ();
}

static void
setup_input_stream (void)
{
  if (input_file == nullptr)
    {
      input_file = _("standard input");
      set_fd_flags (STDIN_FILENO, input_flags, input_file);
    }
  else
    {
      if (ifd_reopen (STDIN_FILENO, input_file, O_RDONLY | input_flags, 0) < 0)
        error (EXIT_FAILURE, errno, _("failed to open %s"),
               quoteaf (input_file));
    }

  off_t offset = lseek (STDIN_FILENO, 0, SEEK_CUR);
  input_seekable = (0 <= offset);
  input_offset = MAX (0, offset);
  input_seek_errno = errno;
}

static int
handle_output_truncation (off_t size)
{
  if (iftruncate (STDOUT_FILENO, size) == 0)
    return EXIT_SUCCESS;

  int ftruncate_errno = errno;
  struct stat stdout_stat;

  if (ifstat (STDOUT_FILENO, &stdout_stat) != 0)
    {
      diagnose (errno, _("cannot fstat %s"), quoteaf (output_file));
      return EXIT_FAILURE;
    }

  if (S_ISREG (stdout_stat.st_mode)
      || S_ISDIR (stdout_stat.st_mode)
      || S_TYPEISSHM (&stdout_stat))
    {
      diagnose (ftruncate_errno,
                _("failed to truncate to %jd bytes in output file %s"),
                (intmax_t) size, quoteaf (output_file));
      return EXIT_FAILURE;
    }

  return EXIT_SUCCESS;
}

static int
setup_output_stream (void)
{
  if (output_file == nullptr)
    {
      output_file = _("standard output");
      set_fd_flags (STDOUT_FILENO, output_flags, output_file);
      return EXIT_SUCCESS;
    }

  mode_t perms = MODE_RW_UGO;
  int opts = output_flags
             | (conversions_mask & C_NOCREAT ? 0 : O_CREAT)
             | (conversions_mask & C_EXCL ? O_EXCL : 0)
             | (seek_records || (conversions_mask & C_NOTRUNC) ? 0 : O_TRUNC);

  off_t size;
  if ((ckd_mul (&size, seek_records, output_blocksize)
       || ckd_add (&size, seek_bytes, size))
      && !(conversions_mask & C_NOTRUNC))
    {
      error (EXIT_FAILURE, 0,
             _("offset too large: cannot truncate to a length of seek=%jd"
               " (%td-byte) blocks"),
             seek_records, output_blocksize);
    }

  bool opened = false;
  if (seek_records)
    {
      if (ifd_reopen (STDOUT_FILENO, output_file, O_RDWR | opts, perms) >= 0)
        opened = true;
    }

  if (!opened && ifd_reopen (STDOUT_FILENO, output_file, O_WRONLY | opts, perms) < 0)
    error (EXIT_FAILURE, errno, _("failed to open %s"), quoteaf (output_file));

  if (seek_records != 0 && !(conversions_mask & C_NOTRUNC))
    return handle_output_truncation (size);

  return EXIT_SUCCESS;
}

static int
handle_cache_invalidation (void)
{
  int status = EXIT_SUCCESS;
  if (max_records == 0 && max_bytes == 0)
    {
      if (i_nocache && !invalidate_cache (STDIN_FILENO, 0))
        {
          diagnose (errno, _("failed to discard cache for: %s"),
                    quotef (input_file));
          status = EXIT_FAILURE;
        }
      if (o_nocache && !invalidate_cache (STDOUT_FILENO, 0))
        {
          diagnose (errno, _("failed to discard cache for: %s"),
                    quotef (output_file));
          status = EXIT_FAILURE;
        }
    }
  else
    {
      if (i_nocache || i_nocache_eof)
        invalidate_cache (STDIN_FILENO, 0);
      if (o_nocache || o_nocache_eof)
        invalidate_cache (STDOUT_FILENO, 0);
    }
  return status;
}

int
main (int argc, char **argv)
{
  int exit_status = EXIT_SUCCESS;

  initialize_program (&argc, &argv);

  setup_input_stream ();
  if (setup_output_stream () != EXIT_SUCCESS)
    exit_status = EXIT_FAILURE;

  start_time = gethrxtime ();
  next_time = start_time + XTIME_PRECISION;

  int copy_status = dd_copy ();
  if (copy_status != EXIT_SUCCESS)
    exit_status = copy_status;

  int sync_status = synchronize_output ();
  if (sync_status != EXIT_SUCCESS)
    exit_status = sync_status;

  if (handle_cache_invalidation () != EXIT_SUCCESS)
    exit_status = EXIT_FAILURE;

  finish_up ();
  main_exit (exit_status);
}
