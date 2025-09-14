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
  else
    {
      /* If stdout closure is not required, attempt to close stderr. */
      if (close_stream (stderr) != 0)
        {
          /* If stderr closure fails, terminate the program immediately. */
          _exit (EXIT_FAILURE);
        }
    }
}

/* Like the 'error' function but handle any pending newline,
   and do not exit.  */

ATTRIBUTE_FORMAT ((__printf__, 2, 3))
static void
diagnose (int errnum, char const *fmt, ...)
{
  if (progress_len > 0)
    {
      fputc ('\n', stderr);
      progress_len = 0;
    }

  va_list ap;
  va_start (ap, fmt);
  verror (0, errnum, fmt, ap);
  va_end (ap);
}

#include <stdio.h>
#include <stdlib.h>

static void
print_usage_synopsis(void)
{
  printf (_("\
Usage: %s [OPERAND]...\n\
  or:  %s OPTION\n\
"),
          program_name, program_name);
  fputs (_("\
Copy a file, converting and formatting according to the operands.\n\
\n\
"), stdout);
}

static void
print_operand_descriptions(void)
{
  fputs (_("\
  bs=BYTES        read and write up to BYTES bytes at a time (default: 512);\n\
                  overrides ibs and obs\n\
  cbs=BYTES       convert BYTES bytes at a time\n\
  conv=CONVS      convert the file as per the comma separated symbol list\n\
  count=N         copy only N input blocks\n\
  ibs=BYTES       read up to BYTES bytes at a time (default: 512)\n\
  if=FILE         read from FILE instead of standard input\n\
  iflag=FLAGS     read as per the comma separated symbol list\n\
  obs=BYTES       write BYTES bytes at a time (default: 512)\n\
  of=FILE         write to FILE instead of standard output\n\
  oflag=FLAGS     write as per the comma separated symbol list\n\
  seek=N          (or oseek=N) skip N obs-sized output blocks\n\
  skip=N          (or iseek=N) skip N ibs-sized input blocks\n\
  status=LEVEL    The LEVEL of information to print to standard error;\n\
                  'none' suppresses everything but error messages,\n\
                  'noxfer' suppresses the final transfer statistics,\n\
                  'progress' shows periodic transfer statistics\n\
"), stdout);
}

static void
print_multiplicative_suffixes(void)
{
  fputs (_("\
\n\
N and BYTES may be followed by the following multiplicative suffixes:\n\
c=1, w=2, b=512, kB=1000, K=1024, MB=1000*1000, M=1024*1024, xM=M,\n\
GB=1000*1000*1000, G=1024*1024*1024, and so on for T, P, E, Z, Y, R, Q.\n\
Binary prefixes can be used, too: KiB=K, MiB=M, and so on.\n\
If N ends in 'B', it counts bytes not blocks.\n\
\n\
"), stdout);
}

static void
print_conv_symbols_description(void)
{
  fputs (_("Each CONV symbol may be:\n\n"), stdout);
  fputs (_("\
  ascii     from EBCDIC to ASCII\n\
  ebcdic    from ASCII to EBCDIC\n\
  ibm       from ASCII to alternate EBCDIC\n\
  block     pad newline-terminated records with spaces to cbs-size\n\
  unblock   replace trailing spaces in cbs-size records with newline\n\
  lcase     change upper case to lower case\n\
  ucase     change lower case to upper case\n\
  sparse    try to seek rather than write all-NUL output blocks\n\
  swab      swap every pair of input bytes\n\
  sync      pad every input block with NULs to ibs-size; when used\n\
            with block or unblock, pad with spaces rather than NULs\n\
  excl      fail if the output file already exists\n\
  nocreat   do not create the output file\n\
  notrunc   do not truncate the output file\n\
  noerror   continue after read errors\n\
  fdatasync  physically write output file data before finishing\n\
  fsync     likewise, but also write metadata\n\
"), stdout);
}

static void
print_flag_symbols_description(void)
{
  fputs (_("\nEach FLAG symbol may be:\n\n"), stdout);
  fputs (_("  append    append mode (makes sense only for output; conv=notrunc suggested)\n"), stdout);
  if (O_CIO)
    fputs (_("  cio       use concurrent I/O for data\n"), stdout);
  if (O_DIRECT)
    fputs (_("  direct    use direct I/O for data\n"), stdout);
  fputs (_("  directory  fail unless a directory\n"), stdout);
  if (O_DSYNC)
    fputs (_("  dsync     use synchronized I/O for data\n"), stdout);
  if (O_SYNC)
    fputs (_("  sync      likewise, but also for metadata\n"), stdout);
  fputs (_("  fullblock  accumulate full blocks of input (iflag only)\n"), stdout);
  if (O_NONBLOCK)
    fputs (_("  nonblock  use non-blocking I/O\n"), stdout);
  if (O_NOATIME)
    fputs (_("  noatime   do not update access time\n"), stdout);
#if HAVE_POSIX_FADVISE
  if (O_NOCACHE)
    fputs (_("  nocache   Request to drop cache.  See also oflag=sync\n"), stdout);
#endif
  if (O_NOCTTY)
    fputs (_("  noctty    do not assign controlling terminal from file\n"), stdout);
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
print_signal_handling_info(void)
{
  printf (_("\
\n\
Sending a %s signal to a running 'dd' process makes it\n\
print I/O statistics to standard error and then resume copying.\n\
\n\
Options are:\n\
\n\
"), SIGINFO == SIGUSR1 ? "USR1" : "INFO");
}

static void
print_standard_options(void)
{
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
      print_usage_synopsis();
      print_operand_descriptions();
      print_multiplicative_suffixes();
      print_conv_symbols_description();
      print_flag_symbols_description();
      print_signal_handling_info();
      print_standard_options();
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
    return;

  if (input_blocksize < 0)
    {
      error (EXIT_FAILURE, 0, _("internal error: input block size cannot be negative"));
    }

  bool const needs_extra_byte = (conversions_mask & C_SWAB) != 0;

  size_t requested_size = (size_t)input_blocksize;

  if (needs_extra_byte)
    {
      if (requested_size == SIZE_MAX)
        {
          error (EXIT_FAILURE, 0, _("requested input buffer size too large"));
        }
      requested_size++;
    }

  ibuf = alignalloc (page_size, requested_size);

  if (!ibuf)
    {
      char hbuf[LONGEST_HUMAN_READABLE + 1];
      error (EXIT_FAILURE, 0,
             _("memory exhausted by input buffer of size %zu bytes (%s)"),
             requested_size,
             human_readable (requested_size, hbuf,
                             human_opts | human_base_1024, 1, 1));
    }
}

/* Ensure output buffer OBUF is allocated/initialized.  */

static void
alloc_obuf (void)
{
  if (obuf)
    return;

  if (conversions_mask & C_TWOBUFS)
    {
      obuf = alignalloc (page_size, output_blocksize);
      if (!obuf)
        {
          char hbuf[LONGEST_HUMAN_READABLE + 1];
          error (EXIT_FAILURE, 0,
                 _("memory exhausted by output buffer of size %td"
                   " bytes (%s)"),
                 output_blocksize,
                 human_readable (output_blocksize, hbuf,
                                 human_opts | human_base_1024, 1, 1));
        }
    }
  else
    {
      alloc_ibuf ();
      obuf = ibuf;
      if (!obuf)
        {
          char hbuf[LONGEST_HUMAN_READABLE + 1];
          error (EXIT_FAILURE, 0,
                 _("memory exhausted by shared input/output buffer of size %td"
                   " bytes (%s)"),
                 output_blocksize,
                 human_readable (output_blocksize, hbuf,
                                 human_opts | human_base_1024, 1, 1));
        }
    }
}

#include <stddef.h>
#include <limits.h>

static void
translate_charset (char const *new_trans)
{
  if (new_trans == NULL)
    {
      return;
    }

  const size_t charset_size = UCHAR_MAX + 1;

  for (size_t i = 0; i < charset_size; i++)
    {
      unsigned char current_idx = (unsigned char)trans_table[i];
      trans_table[i] = new_trans[current_idx];
    }
  translation_needed = true;
}

/* Return true if I has more than one bit set.  I must be nonnegative.  */

static inline bool
multiple_bits_set (int i)
{
  return i != 0 && (i & (i - 1)) != 0;
}

#include <string.h>
#include <stdbool.h>

static bool
abbreviation_lacks_prefix (char const *message)
{
  if (message == NULL) {
    return false;
  }

  size_t len = strlen(message);

  if (len < 2) {
    return false;
  }

  return message[len - 2] == ' ';
}

/* Print transfer statistics.  */

static void
print_xfer_stats (xtime_t progress_time)
{
  xtime_t now = progress_time ? progress_time : gethrxtime ();
  static char const slash_s[] = "/s";
  char hbuf[3][LONGEST_HUMAN_READABLE + sizeof slash_s];
  double delta_s;
  char const *bytes_per_second_final;

  char const *si = human_readable (w_bytes, hbuf[0], human_opts, 1, 1);
  char const *iec = human_readable (w_bytes, hbuf[1],
                                    human_opts | human_base_1024, 1, 1);

  char *bpsbuf_writeable = hbuf[2];
  int bpsbufsize = sizeof hbuf[2];

  if (start_time < now)
    {
      xtime_t delta_xtime = now - start_time;
      delta_s = (double)delta_xtime / XTIME_PRECISION;

      // Call human_readable to fill bpsbuf_writeable with the rate value and its unit (e.g., "1.2 M")
      (void)human_readable (w_bytes, bpsbuf_writeable, human_opts,
                            XTIME_PRECISION, delta_xtime);

      size_t current_len = strlen(bpsbuf_writeable);
      // Safely append "/s" to the formatted string using snprintf
      // Ensure there's space for "/s" and the null terminator.
      if (current_len + sizeof(slash_s) <= (size_t)bpsbufsize) {
          snprintf(bpsbuf_writeable + current_len, bpsbufsize - current_len, "%s", slash_s);
      } else {
          // Buffer is too small, string will be truncated or overflow.
          // For legacy code, just ensure null termination if snprintf truncates.
          // In a new design, consider error handling or larger buffer.
          // Original code would have caused a buffer overflow with strcat.
      }
      bytes_per_second_final = bpsbuf_writeable;
    }
  else
    {
      delta_s = 0;
      // Format "Infinity B/s" directly into bpsbuf_writeable
      snprintf (bpsbuf_writeable, bpsbufsize, "%s B/s", _("Infinity"));
      bytes_per_second_final = bpsbuf_writeable;
    }

  if (progress_time)
    fputc ('\r', stderr);

  char delta_s_buf[24];
  // snprintf return value is not checked as per original code's error handling level.
  // Buffer size 24 is assumed sufficient for "%.0f s" or "%g s".
  snprintf (delta_s_buf, sizeof delta_s_buf,
            progress_time ? "%.0f s" : "%g s", delta_s);

  char const *format_string;
  char const *extra_arg1 = NULL;
  char const *extra_arg2 = NULL;
  int num_extra_args = 0;

  if (abbreviation_lacks_prefix(si)) {
    format_string = ngettext ("%jd byte copied, %s, %s",
                              "%jd bytes copied, %s, %s",
                              select_plural (w_bytes));
  } else if (abbreviation_lacks_prefix(iec)) {
    format_string = _("%jd bytes (%s) copied, %s, %s");
    extra_arg1 = si;
    num_extra_args = 1;
  } else {
    format_string = _("%jd bytes (%s, %s) copied, %s, %s");
    extra_arg1 = si;
    extra_arg2 = iec;
    num_extra_args = 2;
  }

  int stats_len;
  // Cast w_bytes to long long for %jd specifier safety.
  if (num_extra_args == 0) {
      stats_len = fprintf(stderr, format_string,
                          (long long)w_bytes, delta_s_buf, bytes_per_second_final);
  } else if (num_extra_args == 1) {
      stats_len = fprintf(stderr, format_string,
                          (long long)w_bytes, extra_arg1, delta_s_buf, bytes_per_second_final);
  } else { // num_extra_args == 2
      stats_len = fprintf(stderr, format_string,
                          (long long)w_bytes, extra_arg1, extra_arg2, delta_s_buf, bytes_per_second_final);
  }

  if (progress_time)
    {
      if (0 <= stats_len && stats_len < progress_len)
        fprintf (stderr, "%*s", progress_len - stats_len, "");
      progress_len = stats_len;
    }
  else
    fputc ('\n', stderr);

  reported_w_bytes = w_bytes;
}

static void
print_stats (void)
{
  if (status_level == STATUS_NONE)
    return;

  if (progress_len > 0)
    {
      fputc ('\n', stderr);
      progress_len = 0;
    }

  fprintf (stderr,
           _("%jd+%jd records in\n"
             "%jd+%jd records out\n"),
           r_full, r_partial, w_full, w_partial);

  if (r_truncate > 0)
    fprintf (stderr,
             ngettext ("%jd truncated record\n",
                       "%jd truncated records\n",
                       select_plural (r_truncate)),
             r_truncate);

  if (status_level == STATUS_NOXFER)
    return;

  print_xfer_stats (0);
}

/* An ordinary signal was received; arrange for the program to exit.  */

#include <signal.h> // For sigaction, sigemptyset, SIG_DFL, sig_atomic_t

// The `interrupt_signal` variable is assumed to be defined globally elsewhere
// in the legacy code. For safety and correctness in a signal handler,
// it must be declared as `volatile sig_atomic_t`.
// Initializing it to 0 is good practice to prevent uninitialized access.
static volatile sig_atomic_t interrupt_signal = 0;

// The `SA_RESETHAND` symbol from the original code is interpreted here
// as a preprocessor macro. The `#if !SA_RESETHAND` directive precisely
// replicates the conditional behavior of `if (! SA_RESETHAND)` at compile-time.
// If `SA_RESETHAND` is undefined or evaluates to 0, the block of code is included.
// If `SA_RESETHAND` is defined to a non-zero value, the block is excluded.
static void
interrupt_handler (int sig)
{
#if !SA_RESETHAND
  struct sigaction sa_default;

  // Set the handler to the default action for the signal.
  sa_default.sa_handler = SIG_DFL;
  // Clear the signal mask, ensuring no signals are blocked while handling.
  sigemptyset(&sa_default.sa_mask);
  // No special flags are required when setting the default action.
  sa_default.sa_flags = 0;

  // Replace the less reliable `signal()` function with `sigaction()` for setting
  // the signal disposition to default.
  // Calling `sigaction()` from within a signal handler for the same signal is
  // generally not considered async-signal-safe by POSIX standards. However,
  // the original code's explicit functionality requires this conditional reset
  // to occur within the handler. This refactoring improves the API choice
  // from `signal()` to `sigaction()`, while maintaining the original behavior.
  // In a truly ideal scenario, this reset behavior would be configured via the
  // `SA_RESETHAND` flag when the handler is initially registered with `sigaction()`,
  // thereby avoiding modifications to signal disposition from within the handler itself.
  if (sigaction(sig, &sa_default, NULL) == -1)
  {
    // The original code did not include error handling for `signal()`.
    // In a production system, an async-signal-safe logging mechanism
    // or a `volatile sig_atomic_t` error flag would be appropriate here.
  }
#endif

  // Assign the received signal number to the global variable.
  // This operation is async-signal-safe due to `interrupt_signal` being
  // declared as `volatile sig_atomic_t`.
  interrupt_signal = sig;
}

/* An info signal was received; arrange for the program to print status.  */

static void
siginfo_handler (int sig)
{
  info_signal_count++;
}

/* Install the signal handlers.  */

static void
install_signal_handlers (void)
{
  bool catch_siginfo = ! (SIGINFO == SIGUSR1 && getenv ("POSIXLY_CORRECT"));

#if SA_NOCLDSTOP

  struct sigaction act;
  sigset_t handler_mask;

  sigemptyset (&handler_mask);

  if (catch_siginfo)
    {
      sigaddset (&handler_mask, SIGINFO);
    }

  struct sigaction old_sigint_act;
  if (sigaction (SIGINT, NULL, &old_sigint_act) == -1)
    {
      perror ("sigaction(SIGINT, NULL)");
      return;
    }

  bool sigint_was_not_ignored = (old_sigint_act.sa_handler != SIG_IGN);
  if (sigint_was_not_ignored)
    {
      sigaddset (&handler_mask, SIGINT);
    }

  if (catch_siginfo)
    {
      memset (&act, 0, sizeof (act));
      act.sa_handler = siginfo_handler;
      act.sa_mask = handler_mask;
      act.sa_flags = 0;
      if (sigaction (SIGINFO, &act, NULL) == -1)
        {
          perror ("sigaction(SIGINFO)");
          return;
        }
    }

  if (sigint_was_not_ignored)
    {
      memset (&act, 0, sizeof (act));
      act.sa_handler = interrupt_handler;
      act.sa_mask = handler_mask;
      act.sa_flags = SA_NODEFER | SA_RESETHAND;
      if (sigaction (SIGINT, &act, NULL) == -1)
        {
          perror ("sigaction(SIGINT)");
          return;
        }
    }

#else /* SA_NOCLDSTOP is not defined */

  if (catch_siginfo)
    {
      if (signal (SIGINFO, siginfo_handler) == SIG_ERR)
        {
          perror ("signal(SIGINFO)");
          return;
        }
      if (siginterrupt (SIGINFO, 1) == -1)
        {
          perror ("siginterrupt(SIGINFO)");
          return;
        }
    }

  if (signal (SIGINT, SIG_IGN) != SIG_IGN)
    {
      if (signal (SIGINT, interrupt_handler) == SIG_ERR)
        {
          perror ("signal(SIGINT)");
          return;
        }
      if (siginterrupt (SIGINT, 1) == -1)
        {
          perror ("siginterrupt(SIGINT)");
          return;
        }
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
handle_file_descriptor_close(int fd, const char* filename_for_error_msg)
{
  if (iclose(fd) != 0)
    error(EXIT_FAILURE, errno, _("closing file %s"), quoteaf(filename_for_error_msg));
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

  handle_file_descriptor_close(STDIN_FILENO, input_file);
  handle_file_descriptor_close(STDOUT_FILENO, output_file);
}

/* Process any pending signals.  If signals are caught, this function
   should be called periodically.  Ideally there should never be an
   unbounded amount of time when signals are not being processed.  */

static void
process_signals (void)
{
  while (interrupt_signal || info_signal_count)
    {
      int interrupt_flag;
      int info_count_snapshot;
      sigset_t old_mask;

      sigprocmask (SIG_BLOCK, &caught_signals, &old_mask);

      interrupt_flag = interrupt_signal;
      info_count_snapshot = info_signal_count;

      if (info_count_snapshot > 0)
        {
          info_signal_count = info_count_snapshot - 1;
        }

      sigprocmask (SIG_SETMASK, &old_mask, NULL);

      if (interrupt_flag)
        {
          cleanup ();
        }
      print_stats ();
      if (interrupt_flag)
        {
          raise (interrupt_flag);
        }
    }
}

static void
finish_up (void)
{
  static int has_run = 0;

  if (has_run) {
    return;
  }
  has_run = 1;

  process_signals ();
  cleanup ();
  print_stats ();
}

#include <stdlib.h>

static void
quit (int code)
{
  finish_up ();
  exit (code);
}

/* Return LEN rounded down to a multiple of IO_BUFSIZE
   (to minimize calls to the expensive posix_fadvise (,POSIX_FADV_DONTNEED),
   while storing the remainder internally per FD.
   Pass LEN == 0 to get the current remainder.  */

static off_t
cache_round (int fd, off_t input_len)
{
  static off_t s_input_pending_bytes = 0;
  static off_t s_output_pending_bytes = 0;

  off_t *current_pending_ptr;
  if (fd == STDIN_FILENO) {
    current_pending_ptr = &s_input_pending_bytes;
  } else {
    current_pending_ptr = &s_output_pending_bytes;
  }

  off_t result_len;

  if (input_len != 0)
    {
      intmax_t total_accumulated_len;
      if (ckd_add (&total_accumulated_len, *current_pending_ptr, input_len))
        {
          total_accumulated_len = INTMAX_MAX;
        }

      *current_pending_ptr = (off_t)(total_accumulated_len % IO_BUFSIZE);
      result_len = (off_t)(total_accumulated_len - *current_pending_ptr);
    }
  else
    {
      result_len = *current_pending_ptr;
    }

  return result_len;
}

/* Discard the cache from the current offset of either
   STDIN_FILENO or STDOUT_FILENO.
   Return true on success.
   Return false on failure, with errno set.  */

#include <unistd.h>
#include <errno.h>
#include <stdbool.h>

#if HAVE_POSIX_FADVISE
#include <fcntl.h>
#endif

#define OFF_T_UNINITIALIZED ((off_t)-2)

static off_t
get_file_offset(int fd)
{
    return lseek(fd, 0, SEEK_CUR);
}

static bool
invalidate_cache(int fd, off_t len)
{
    extern bool i_nocache_eof;
    extern bool o_nocache_eof;
    extern bool input_seekable;
    extern off_t input_offset;
    extern off_t page_size;
    extern off_t cache_round(int fd, off_t len_or_zero);

    const bool is_stdin = (fd == STDIN_FILENO);
    const bool nocache_eof = is_stdin ? i_nocache_eof : o_nocache_eof;

    const off_t clen_rounded = cache_round(fd, len);
    const off_t pending_rounded = (len > 0) ? cache_round(fd, 0) : 0;

    if (len > 0 && clen_rounded == 0) {
        return true;
    }
    if (len == 0 && clen_rounded == 0 && !nocache_eof) {
        return true;
    }

    off_t current_file_offset;

    if (is_stdin) {
        if (!input_seekable) {
            errno = ESPIPE;
            return false;
        }
        current_file_offset = input_offset;
    } else {
        static off_t tracked_output_offset = OFF_T_UNINITIALIZED;

        if (tracked_output_offset == OFF_T_UNINITIALIZED) {
            tracked_output_offset = get_file_offset(fd);
            if (tracked_output_offset == (off_t)-1) {
                return false;
            }
        } else if (len > 0) {
            tracked_output_offset += clen_rounded + pending_rounded;
        }
        current_file_offset = tracked_output_offset;
    }

    if (current_file_offset == (off_t)-1) {
        return false;
    }

    off_t advise_start_offset;
    off_t advise_length;

    if (len == 0 && clen_rounded > 0 && nocache_eof) {
        advise_start_offset = current_file_offset - clen_rounded;
        advise_length = 0;
    } else {
        advise_start_offset = current_file_offset - (clen_rounded + pending_rounded);
        advise_length = clen_rounded;
    }

#if HAVE_POSIX_FADVISE
    if (advise_length == 0) {
        advise_start_offset -= advise_start_offset % page_size;
    }

    const int adv_ret = posix_fadvise(fd, advise_start_offset, advise_length, POSIX_FADV_DONTNEED);
    if (adv_ret != 0) {
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
iread (int fd, char *buf, idx_t size, ssize_t *prev_nread_ptr, bool *warn_partial_read_ptr)
{
  ssize_t nread;

  do
    {
      process_signals ();
      nread = read (fd, buf, size);
      if (nread == -1 && errno == EINVAL
          && 0 < *prev_nread_ptr && *prev_nread_ptr < size
          && (input_flags & O_DIRECT))
        {
          errno = 0;
          nread = 0;
        }
    }
  while (nread < 0 && errno == EINTR);

  if (0 < nread && nread < size)
    process_signals ();

  if (0 < nread && *warn_partial_read_ptr)
    {
      if (0 < *prev_nread_ptr && *prev_nread_ptr < size)
        {
          idx_t prev = *prev_nread_ptr;
          if (status_level != STATUS_NONE)
            diagnose (0, ngettext (("warning: partial read (%td byte); "
                                    "suggest iflag=fullblock"),
                                   ("warning: partial read (%td bytes); "
                                    "suggest iflag=fullblock"),
                                   select_plural (prev)),
                      prev);
          *warn_partial_read_ptr = false;
        }
    }

  *prev_nread_ptr = nread;
  return nread;
}

/* Wrapper around iread function to accumulate full blocks.  */
static ssize_t
iread_fullblock (int fd, char *buf, idx_t size)
{
  ssize_t total_bytes_read = 0;
  idx_t   bytes_remaining  = size;
  char   *current_buf_pos  = buf;

  while (bytes_remaining > 0)
    {
      ssize_t bytes_read_this_call = iread(fd, current_buf_pos, bytes_remaining);

      if (bytes_read_this_call < 0)
        return bytes_read_this_call;
      if (bytes_read_this_call == 0)
        break;

      total_bytes_read   += bytes_read_this_call;
      current_buf_pos    += bytes_read_this_call;
      bytes_remaining    -= bytes_read_this_call;
    }

  return total_bytes_read;
}

/* Write to FD the buffer BUF of size SIZE, processing any signals
   that arrive.  Return the number of bytes written, setting errno if
   this is less than SIZE.  Keep trying if there are partial
   writes.  */

static idx_t
iwrite (int fd, char const *buf, idx_t size)
{
  idx_t total_written = 0;

  if ((output_flags & O_DIRECT) && size < output_blocksize)
    {
      int old_flags = fcntl (STDOUT_FILENO, F_GETFL);
      if (old_flags == -1)
        {
          if (status_level != STATUS_NONE)
            diagnose (errno, _("failed to get flags for stdout: %s"), quotef (output_file));
        }
      else
        {
          if (fcntl (STDOUT_FILENO, F_SETFL, old_flags & ~O_DIRECT) == -1)
            {
              if (status_level != STATUS_NONE)
                diagnose (errno, _("failed to turn off O_DIRECT for stdout: %s"), quotef (output_file));
            }
          else
            {
              o_nocache_eof = true;
              invalidate_cache (STDOUT_FILENO, 0);
              conversions_mask |= C_FSYNC;
            }
        }
    }

  while (total_written < size)
    {
      ssize_t nwritten_this_iteration = 0;
      process_signals ();

      final_op_was_seek = false;
      if ((conversions_mask & C_SPARSE) && is_nul (buf, size))
        {
          if (lseek (fd, size, SEEK_CUR) < 0)
            {
              conversions_mask &= ~C_SPARSE;
            }
          else
            {
              final_op_was_seek = true;
              nwritten_this_iteration = size;
            }
        }

      if (nwritten_this_iteration == 0)
        nwritten_this_iteration = write (fd, buf + total_written, size - total_written);

      if (nwritten_this_iteration < 0)
        {
          if (errno != EINTR)
            break;
        }
      else if (nwritten_this_iteration == 0)
        {
          errno = ENOSPC;
          break;
        }
      else
        {
          total_written += nwritten_this_iteration;
        }
    }

  if (o_nocache && total_written)
    invalidate_cache (fd, total_written);

  return total_written;
}

/* Write, then empty, the output buffer 'obuf'. */

static void
write_output (void)
{
  ssize_t raw_nwritten = iwrite (STDOUT_FILENO, obuf, output_blocksize);
  
  idx_t actual_nwritten;
  if (raw_nwritten < 0)
    {
      actual_nwritten = 0;
    }
  else
    {
      actual_nwritten = (idx_t)raw_nwritten;
    }

  w_bytes += actual_nwritten;

  if (actual_nwritten == output_blocksize)
    {
      w_full++;
    }
  else
    {
      diagnose (errno, _("writing to %s"), quoteaf (output_file));
      if (actual_nwritten > 0)
        w_partial++;
      quit (EXIT_FAILURE);
    }
  
  oc = 0;
}

/* Restart on EINTR from fdatasync.  */

#include <unistd.h>
#include <errno.h>

extern void process_signals(void);

static int
ifdatasync (int fd)
{
  int ret;

  do
    {
      process_signals ();
      ret = fdatasync (fd);
    }
  while (ret < 0 && errno == EINTR);

  return ret;
}

/* Restart on EINTR from fd_reopen.  */

static int
ifd_reopen (int desired_fd, char const *file, int flag, mode_t mode)
{
  int ret;

  for (;;)
    {
      process_signals ();
      ret = fd_reopen (desired_fd, file, flag, mode);

      if (ret >= 0 || errno != EINTR)
        {
          break;
        }
    }

  return ret;
}

/* Restart on EINTR from fstat.  */

static int
ifstat (int fd, struct stat *st)
{
  int ret;

  for (;;)
    {
      process_signals ();
      ret = fstat (fd, st);
      if (ret >= 0 || errno != EINTR)
        {
          break;
        }
    }

  return ret;
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
      if (ret == 0)
        {
          break;
        }
      if (errno != EINTR)
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

  do
    {
      process_signals ();
      ret = ftruncate (fd, length);
    }
  while (ret == -1 && errno == EINTR);

  return ret;
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
parse_symbols (char const *input_str, struct symbol_value const *table,
               bool exclusive, char const *error_msgid)
{
  int result_value = 0;
  char const *current_segment_start = input_str;

  while (true)
    {
      char const *segment_end_ptr = strchr (current_segment_start, ',');
      struct symbol_value const *current_entry;
      bool segment_matched = false;

      for (current_entry = table; current_entry->symbol[0] != '\0'; current_entry++)
        {
          if (operand_matches (current_segment_start, current_entry->symbol, ',') && current_entry->value)
            {
              if (exclusive)
                result_value = current_entry->value;
              else
                result_value |= current_entry->value;
              segment_matched = true;
              break;
            }
        }

      if (!segment_matched)
        {
          idx_t segment_len = segment_end_ptr ? (idx_t)(segment_end_ptr - current_segment_start) : (idx_t)strlen (current_segment_start);
          diagnose (0, "%s: %s", _(error_msgid),
                    quotearg_n_style_mem (0, locale_quoting_style,
                                          current_segment_start, segment_len));
          usage (EXIT_FAILURE);
        }

      if (segment_end_ptr == NULL)
        break;

      current_segment_start = segment_end_ptr + 1;
    }

  return result_value;
}

/* Return the value of STR, interpreted as a non-negative decimal integer,
   optionally multiplied by various values.
   Set *INVALID to an appropriate error value and return INTMAX_MAX if
   it is an overflow, an indeterminate value if some other error occurred.  */

static intmax_t
parse_integer (char const *str, strtol_error *invalid)
{
  uintmax_t n_parsed_value;
  char *suffix;
  static char const suffixes[] = "bcEGkKMPQRTwYZ0";
  strtol_error current_error;

  current_error = xstrtoumax (str, &suffix, 10, &n_parsed_value, suffixes);

  if ((current_error & ~LONGINT_OVERFLOW) == LONGINT_INVALID_SUFFIX_CHAR
      && *suffix == 'B' && str < suffix && suffix[-1] != 'B')
    {
      suffix++;
      if (!*suffix)
        current_error &= ~LONGINT_INVALID_SUFFIX_CHAR;
    }

  intmax_t final_result;

  if ((current_error & ~LONGINT_OVERFLOW) == LONGINT_INVALID_SUFFIX_CHAR
      && *suffix == 'x')
    {
      strtol_error multiplier_error = LONGINT_OK;
      intmax_t multiplier_value = parse_integer (suffix + 1, &multiplier_error);

      if ((multiplier_error & ~LONGINT_OVERFLOW) != LONGINT_OK)
        {
          current_error = multiplier_error;
          final_result = 0;
        }
      else
        {
          intmax_t base_value_as_intmax;
          strtol_error base_conversion_overflow = LONGINT_OK;

          if (n_parsed_value > INTMAX_MAX)
            {
              base_value_as_intmax = INTMAX_MAX;
              base_conversion_overflow = LONGINT_OVERFLOW;
            }
          else
            {
              base_value_as_intmax = (intmax_t)n_parsed_value;
            }

          int multiplication_overflow = ckd_mul (&final_result, base_value_as_intmax, multiplier_value);

          if (multiplication_overflow ||
              (final_result != 0 && ((current_error | multiplier_error | base_conversion_overflow) & LONGINT_OVERFLOW)))
            {
              current_error = LONGINT_OVERFLOW;
              final_result = INTMAX_MAX;
            }
          else
            {
              current_error = LONGINT_OK;

              if (final_result == 0 && STRPREFIX (str, "0x"))
                diagnose (0, _("warning: %s is a zero multiplier; "
                               "use %s if that is intended"),
                          quote_n (0, "0x"), quote_n (1, "00x"));
            }
        }
    }
  else
    {
      if (n_parsed_value <= INTMAX_MAX)
        final_result = (intmax_t)n_parsed_value;
      else
        {
          current_error = LONGINT_OVERFLOW;
          final_result = INTMAX_MAX;
        }
    }

  *invalid = current_error;
  return final_result;
}

/* OPERAND is of the form "X=...".  Return true if X is NAME.  */

ATTRIBUTE_PURE
static bool
operand_is (char const *operand, char const *name)
{
  return operand_matches (operand, name, '=');
}

static void
parse_dd_numeric_option(const char *val_str, idx_t *idx_target, intmax_t *intmax_target,
                        bool *has_B_target, intmax_t min_val, intmax_t max_val)
{
  strtol_error invalid = LONGINT_OK;
  intmax_t n = parse_integer(val_str, &invalid);
  bool has_B = !!strchr(val_str, 'B');

  if (n < min_val)
    invalid = LONGINT_INVALID;
  else if (max_val < n)
    invalid = LONGINT_OVERFLOW;

  if (invalid != LONGINT_OK)
    error(EXIT_FAILURE, invalid == LONGINT_OVERFLOW ? EOVERFLOW : 0,
          "%s: %s", _("invalid number"), quoteaf(val_str));

  if (idx_target)
    *idx_target = (idx_t)n;
  if (intmax_target)
    *intmax_target = n;
  if (has_B_target)
    *has_B_target = has_B;
}

static void
dd_calculate_position_info(intmax_t arg_value, bool is_byte_mode,
                           unsigned int *flags_mask, unsigned int byte_mode_flag_bit,
                           idx_t block_size, intmax_t *records_out, intmax_t *bytes_out,
                           intmax_t default_arg_value_for_no_op)
{
  if (is_byte_mode)
    *flags_mask |= byte_mode_flag_bit;

  if (arg_value == default_arg_value_for_no_op)
    {
      *records_out = default_arg_value_for_no_op;
      if (bytes_out) *bytes_out = 0;
    }
  else if (*flags_mask & byte_mode_flag_bit)
    {
      if (block_size == 0)
        {
          error(EXIT_FAILURE, 0, _("internal error: block size is zero for byte calculation"));
        }
      *records_out = arg_value / block_size;
      if (bytes_out) *bytes_out = arg_value % block_size;
    }
  else
    {
      *records_out = arg_value;
      if (bytes_out) *bytes_out = 0;
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

  const idx_t MAX_BLOCKSIZE_FOR_IO = MIN (IDX_MAX - 1, MIN (SSIZE_MAX, OFF_T_MAX));
  const idx_t MAX_CONVERSION_BLOCKSIZE = MIN (SIZE_MAX, IDX_MAX);

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
        parse_dd_numeric_option(val, &input_blocksize, NULL, NULL, 1, MAX_BLOCKSIZE_FOR_IO);
      else if (operand_is (name, "obs"))
        parse_dd_numeric_option(val, &output_blocksize, NULL, NULL, 1, MAX_BLOCKSIZE_FOR_IO);
      else if (operand_is (name, "bs"))
        parse_dd_numeric_option(val, &blocksize, NULL, NULL, 1, MAX_BLOCKSIZE_FOR_IO);
      else if (operand_is (name, "cbs"))
        parse_dd_numeric_option(val, &conversion_blocksize, NULL, NULL, 1, MAX_CONVERSION_BLOCKSIZE);
      else if (operand_is (name, "skip") || operand_is (name, "iseek"))
        parse_dd_numeric_option(val, NULL, &skip, &skip_B, 0, INTMAX_MAX);
      else if (operand_is (name + (*name == 'o'), "seek"))
        parse_dd_numeric_option(val, NULL, &seek, &seek_B, 0, INTMAX_MAX);
      else if (operand_is (name, "count"))
        parse_dd_numeric_option(val, NULL, &count, &count_B, 0, INTMAX_MAX);
      else
        {
          diagnose (0, _("unrecognized operand %s"), quoteaf (name));
          usage (EXIT_FAILURE);
        }
    }

  if (blocksize)
    {
      input_blocksize = blocksize;
      output_blocksize = blocksize;
    }
  else
    {
      conversions_mask |= C_TWOBUFS;
    }

  if (input_blocksize == 0)
    input_blocksize = DEFAULT_BLOCKSIZE;
  if (output_blocksize == 0)
    output_blocksize = DEFAULT_BLOCKSIZE;
  if (conversion_blocksize == 0)
    conversions_mask &= ~(C_BLOCK | C_UNBLOCK);

  if (input_flags & (O_DSYNC | O_SYNC))
    input_flags |= O_RSYNC;

  if (output_flags & O_FULLBLOCK)
    {
      diagnose (0, "%s: %s", _("invalid output flag"), quote ("fullblock"));
      usage (EXIT_FAILURE);
    }

  dd_calculate_position_info(skip, skip_B, &input_flags, O_SKIP_BYTES,
                             input_blocksize, &skip_records, &skip_bytes, 0);

  dd_calculate_position_info(count, count_B, &input_flags, O_COUNT_BYTES,
                             input_blocksize, &max_records, &max_bytes, INTMAX_MAX);

  dd_calculate_position_info(seek, seek_B, &output_flags, O_SEEK_BYTES,
                             output_blocksize, &seek_records, &seek_bytes, 0);

  warn_partial_read =
    (! (conversions_mask & C_TWOBUFS) && ! (input_flags & O_FULLBLOCK)
     && (skip_records
         || (0 < max_records && max_records < INTMAX_MAX)
         || (input_flags | output_flags) & O_DIRECT));

  iread_fnc = ((input_flags & O_FULLBLOCK)
               ? iread_fullblock
               : iread);
  input_flags &= ~O_FULLBLOCK;

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

/* Fix up translation table. */

static void
apply_case_conversion_to_table(int (*convert_func)(int))
{
  for (int i = 0; i < 256; i++)
    {
      trans_table[i] = (char) convert_func((unsigned char) trans_table[i]);
    }
  translation_needed = true;
}

static void
apply_translations (void)
{
  if (conversions_mask & C_ASCII)
    translate_charset (ebcdic_to_ascii);

  if (conversions_mask & C_UCASE)
    {
      apply_case_conversion_to_table(toupper);
    }
  else if (conversions_mask & C_LCASE)
    {
      apply_case_conversion_to_table(tolower);
    }

  if (conversions_mask & C_EBCDIC)
    {
      translate_charset (ascii_to_ebcdic);
      newline_character = ascii_to_ebcdic['\n'];
      space_character = ascii_to_ebcdic[' '];
    }
  else if (conversions_mask & C_IBM)
    {
      translate_charset (ascii_to_ibm);
      newline_character = ascii_to_ibm['\n'];
      space_character = ascii_to_ibm[' '];
    }
}

/* Apply the character-set translations specified by the user
   to the NREAD bytes in BUF.  */

static void
translate_buffer (char *buf, idx_t nread)
{
  char *end_ptr = buf + nread;
  char *cp;

  for (cp = buf; cp < end_ptr; cp++)
    {
      *cp = trans_table[to_uchar(*cp)];
    }
}

/* Swap *NREAD bytes in BUF, which should have room for an extra byte
   after the end because the swapping is not in-place.  If *SAVED_BYTE
   is nonnegative, also swap that initial byte from the previous call.
   Save the last byte into into *SAVED_BYTE if needed to make the
   resulting *NREAD even, and set *SAVED_BYTE to -1 otherwise.
   Return the buffer's adjusted start, either BUF or BUF + 1.  */

#include <stddef.h>

#define NO_SAVED_BYTE -1

static char *
swab_buffer (char *buf, idx_t *nread, int *saved_byte)
{
  if (*nread == 0)
    return buf;

  int prev_saved_value = *saved_byte;

  if ((prev_saved_value == NO_SAVED_BYTE && (*nread % 2 != 0)) ||
      (prev_saved_value != NO_SAVED_BYTE && (*nread % 2 == 0)))
  {
    unsigned char last_byte = buf[--*nread];
    *saved_byte = last_byte;
  }
  else
  {
    *saved_byte = NO_SAVED_BYTE;
  }

  for (idx_t i = *nread; i > 1; i -= 2)
  {
    buf[i] = buf[i - 2];
  }

  if (prev_saved_value == NO_SAVED_BYTE)
  {
    return buf + 1;
  }
  else
  {
    buf[1] = (char)prev_saved_value;
    ++*nread;
    return buf;
  }
}

/* Add OFFSET to the input offset, setting the overflow flag if
   necessary.  */

static void
advance_input_offset (intmax_t offset)
{
  if (input_offset < 0)
  {
    return;
  }

  if (ckd_add(&input_offset, input_offset, offset))
  {
    input_offset = -1;
  }
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
skip (int fdesc, char const *file, intmax_t records, idx_t blocksize,
      idx_t *bytes)
{
  off_t target_offset_lseek_cur;
  bool ckd_overflow = false;

  // Calculate the target offset. Use checked arithmetic to prevent overflow.
  // If multiplication overflows, no point in attempting lseek, mark as overflow.
  if (ckd_mul(&target_offset_lseek_cur, records, blocksize))
    ckd_overflow = true;
  // If addition overflows, mark as overflow.
  else if (ckd_add_idx(&target_offset_lseek_cur, target_offset_lseek_cur, *bytes))
    ckd_overflow = true;

  // Attempt lseek if calculations did not overflow.
  if (!ckd_overflow)
    {
      errno = 0; // Clear errno before lseek to distinguish its errors.
      if (lseek (fdesc, target_offset_lseek_cur, SEEK_CUR) >= 0)
        {
          // Lseek successful path
          if (fdesc == STDIN_FILENO)
            {
              struct stat st;
              if (ifstat (STDIN_FILENO, &st) != 0)
                error (EXIT_FAILURE, errno, _("cannot fstat %s"), quoteaf (file));

              // Check if skipping past EOF on STDIN
              if (usable_st_size (&st) && st.st_size > 0 && input_offset >= 0 &&
                  (input_offset + target_offset_lseek_cur) > st.st_size)
                {
                  // When skipping past EOF, calculate the number of full blocks that are not skipped.
                  // The amount overshot from EOF is (input_offset + target_offset_lseek_cur) - st.st_size.
                  if (blocksize > 0)
                    records = ((input_offset + target_offset_lseek_cur) - st.st_size) / blocksize;
                  else
                    records = 0; // If blocksize is zero, no full blocks can be considered unskipped.

                  // Advance input_offset to EOF
                  advance_input_offset (st.st_size - input_offset);
                  // Original behavior: *bytes is not explicitly cleared here.
                }
              else
                {
                  // Full skip achieved or cannot determine EOF (e.g., st_size is 0)
                  records = 0;
                  advance_input_offset (target_offset_lseek_cur);
                  *bytes = 0; // All requested bytes are now skipped.
                }
            }
          else
            {
              // Not STDIN_FILENO, lseek was successful. All requested bytes/records skipped.
              records = 0;
              *bytes = 0;
            }
          return records;
        }
      // If lseek failed, errno will be set appropriately by the system call.
    }
  else
    {
      // ckd_overflow was true, meaning arithmetic overflow prevented lseek from being attempted.
      // Simulate lseek failure due to overflow.
      errno = EOVERFLOW;
    }

  // Lseek failed path (either ckd_overflow or actual lseek call failed)
  // Store errno from the failure for consistent error reporting.
  int lseek_failure_errno = errno;

  // Attempt to lseek to SEEK_END to determine if the file is seekable at all.
  // If it is seekable, then the failure was due to the requested offset being too large/invalid.
  if (lseek (fdesc, 0, SEEK_END) >= 0)
    {
      // File is seekable, but the initial requested skip failed (offset too large, invalid, etc.).
      // In this scenario, the original code always quits. Maintain this behavior.
      diagnose (lseek_failure_errno,
                gettext (fdesc == STDIN_FILENO
                         ? N_("%s: cannot skip")
                         : N_("%s: cannot seek")),
                quotef (file));
      quit (EXIT_FAILURE);
    }
  // Else, the file is not seekable (e.g., pipe, terminal) or lseek(0, SEEK_END) also failed.
  // In this case, fall back to reading.

  // Fallback to reading path
  char *buf_ptr;
  if (fdesc == STDIN_FILENO)
    {
      alloc_ibuf ();
      buf_ptr = ibuf;
    }
  else
    {
      alloc_obuf ();
      buf_ptr = obuf;
    }

  do
    {
      size_t bytes_to_read = 0;
      if (records != 0)
        {
          bytes_to_read = blocksize;
        }
      else
        {
          bytes_to_read = *bytes;
        }

      if (bytes_to_read == 0)
        break; // No bytes to read, exit loop.

      ssize_t nread = iread_fnc (fdesc, buf_ptr, bytes_to_read);
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
              // If read fails, use errno from the read operation.
              diagnose (errno, _("error reading %s"), quotef (file));
            }
          quit (EXIT_FAILURE);
        }
      else if (nread == 0)
        {
          break; // EOF reached
        }
      else if (fdesc == STDIN_FILENO)
        {
          advance_input_offset (nread);
        }

      // Adjust remaining records/bytes based on what was actually read.
      if (records != 0)
        {
          // Decrement records, assuming a block (or part of it) was processed.
          records--;
        }
      else
        {
          // If we were primarily skipping *bytes, they are now consumed.
          *bytes = 0;
        }
    }
  while (records || *bytes);

  return records; // Returns number of records NOT skipped (only relevant if EOF hit prematurely during read)
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

  off_t actual_offset = lseek (STDIN_FILENO, 0, SEEK_CUR);

  if (actual_offset < 0)
    {
      // lseek failed to get current position, errno is set by lseek
      diagnose (errno, _("%s: cannot seek"), quotef (input_file));
      return false;
    }

  if (actual_offset == input_offset)
    {
      return true; // Current file offset matches internal tracker
    }

  // Offsets differ, attempt to correct
  off_t diff = input_offset - actual_offset;

  // Check for suspicious difference and warn if appropriate
  if ((diff < 0 || diff > nbytes) && status_level != STATUS_NONE)
    {
      diagnose (0, _("warning: invalid file offset after failed read"));
    }

  if (lseek (STDIN_FILENO, diff, SEEK_CUR) >= 0)
    {
      return true; // Correction successful
    }

  // Correction failed
  if (errno == 0)
    {
      // Special case: lseek failed but errno is 0, implying a deeper issue
      diagnose (0, _("cannot work around kernel bug after all"));
    }
  else
    {
      // Generic lseek failure, errno is set by lseek
      diagnose (errno, _("%s: cannot seek"), quotef (input_file));
    }

  return false;
}

/* Copy NREAD bytes of BUF, with no conversions.  */

static void
copy_simple (char const *buf, idx_t nread)
{
  char const *current_input_position = buf;

  while (nread > 0)
    {
      idx_t bytes_available_in_output_buffer;
      if (oc < output_blocksize)
        {
          bytes_available_in_output_buffer = output_blocksize - oc;
        }
      else
        {
          bytes_available_in_output_buffer = 0;
        }

      idx_t bytes_to_copy_this_chunk = (nread < bytes_available_in_output_buffer
                                        ? nread : bytes_available_in_output_buffer);

      memcpy (obuf + oc, current_input_position, bytes_to_copy_this_chunk);

      nread -= bytes_to_copy_this_chunk;
      current_input_position += bytes_to_copy_this_chunk;
      oc += bytes_to_copy_this_chunk;

      if (oc >= output_blocksize)
        {
          write_output ();
        }
    }
}

/* Copy NREAD bytes of BUF, doing conv=block
   (pad newline-terminated records to 'conversion_blocksize',
   replacing the newline with trailing spaces).  */

static void
copy_with_block (char const *buf, idx_t nread)
{
  for (idx_t i = 0; i < nread; ++i)
    {
      char current_char = buf[i];

      if (current_char == newline_character)
        {
          if (col < conversion_blocksize)
            {
              for (idx_t j = col; j < conversion_blocksize; ++j)
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
copy_with_unblock (char const *buf, idx_t nread)
{
  static idx_t pending_spaces = 0;

  for (idx_t i = 0; i < nread; /* i is incremented explicitly within the loop */ )
    {
      char c = buf[i];

      // Capture the current column position *before* incrementing `col`.
      // This `current_col_pos` represents the 0-indexed column where `c` would logically be placed.
      idx_t current_col_pos = col;

      // Increment `col` unconditionally, mirroring the original `col++` at the start of the loop.
      // `col` now conceptually accounts for the character `c` (or the slot `c` is taking).
      col++;

      // Check if placing `c` at `current_col_pos` would exceed the block size.
      // This condition is true if `current_col_pos` is `conversion_blocksize` or greater,
      // meaning `c` is the (conversion_blocksize + 1)-th character or beyond, and must start a new line.
      if (current_col_pos >= conversion_blocksize)
        {
          output_char (newline_character); // A newline is needed.
          
          col = 0;                      // Reset `col` for the new line.
          pending_spaces = 0;           // Discard any pending spaces from the previous line, they are lost at line end.
          
          // Do not increment `i`. The character `c` (at `buf[i]`) will be re-processed
          // in the next iteration as the first character on the new line.
          continue; // Jump to the next iteration of the `for` loop to re-evaluate `c`.
        }

      // If we reach here, `c` fits on the current line.
      // `col` has already been incremented to reflect its contribution to the line's length.

      if (c == space_character)
        {
          pending_spaces++; // If `c` is a space, buffer it.
        }
      else // `c` is a non-space character
        {
          // If `c` is a non-space, flush any buffered spaces first.
          // These spaces have already been accounted for in the `col` count (incremented when they were first encountered).
          while (pending_spaces > 0)
            {
              output_char (space_character);
              --pending_spaces;
            }
          // Then output the non-space character itself.
          output_char (c);
        }

      // Only advance to the next input character if `c` was processed on the current line
      // (i.e., it didn't cause a line break and `continue` was not executed).
      i++;
    }
}

/* Set the file descriptor flags for FD that correspond to the nonzero bits
   in ADD_FLAGS.  The file's name is NAME.  */

static void
set_fd_flags (int fd, int add_flags, char const *name)
{
  /* Ignore file creation flags that are no-ops on file descriptors.  */
  add_flags &= ~ (O_NOCTTY | O_NOFOLLOW);

  if (add_flags == 0)
    return;

  int old_flags = fcntl (fd, F_GETFL);
  if (old_flags < 0)
    error (EXIT_FAILURE, errno, _("getting flags for %s"), quoteaf (name));

  // Determine which flags from add_flags are for validation vs. actual setting.
  // O_DIRECTORY and O_NOLINKS are validation flags and are not set via F_SETFL.
  int flags_for_validation = add_flags & (O_DIRECTORY | O_NOLINKS);
  int flags_to_set = add_flags & ~flags_for_validation;

  if (flags_for_validation)
    {
      struct stat st;
      if (ifstat (fd, &st) != 0)
        error (EXIT_FAILURE, errno, _("getting file status for %s"), quoteaf (name));

      if ((flags_for_validation & O_DIRECTORY) && !S_ISDIR (st.st_mode))
        {
          errno = ENOTDIR;
          error (EXIT_FAILURE, errno, _("file is not a directory for %s"), quoteaf (name));
        }
      if ((flags_for_validation & O_NOLINKS) && 1 < st.st_nlink)
        {
          errno = EMLINK;
          error (EXIT_FAILURE, errno, _("file has too many links for %s"), quoteaf (name));
        }
    }

  // Calculate the final flags that would be set on the file descriptor.
  int final_new_flags = old_flags | flags_to_set;

  // Only attempt to set flags if they are actually changing.
  if (old_flags != final_new_flags)
    {
      if (fcntl (fd, F_SETFL, final_new_flags) == -1)
        error (EXIT_FAILURE, errno, _("setting flags for %s"), quoteaf (name));
    }
}

/* The main loop.  */

static inline char get_padding_char(void) {
    return (conversions_mask & (C_BLOCK | C_UNBLOCK)) ? ' ' : '\0';
}

static bool handle_initial_skipping_input_phase(int *exit_status_ptr) {
    if (skip_records == 0 && skip_bytes == 0) {
        return true;
    }

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
        *exit_status_ptr = EXIT_FAILURE;
    }
    return true;
}

static bool handle_initial_seeking_output_phase(int *exit_status_ptr) {
    if (seek_records == 0 && seek_bytes == 0) {
        return true;
    }

    idx_t bytes_to_seek = seek_bytes;
    intmax_t write_records = skip (STDOUT_FILENO, output_file,
                                    seek_records, output_blocksize, &bytes_to_seek);

    if (write_records != 0 || bytes_to_seek != 0) {
        memset (obuf, 0, write_records ? output_blocksize : bytes_to_seek);

        do {
            idx_t size = write_records ? output_blocksize : bytes_to_seek;
            if (iwrite (STDOUT_FILENO, obuf, size) != size) {
                diagnose (errno, _("writing to %s"), quoteaf (output_file));
                *exit_status_ptr = EXIT_FAILURE;
                return false;
            }

            if (write_records != 0)
                write_records--;
            else
                bytes_to_seek = 0;
        } while (write_records || bytes_to_seek);
    }
    return true;
}

static inline bool should_continue_copying_loop(void) {
    return r_partial + r_full < max_records + (max_bytes != 0);
}

static inline void check_and_print_progress(void) {
    if (status_level == STATUS_PROGRESS) {
        xtime_t progress_time = gethrxtime ();
        if (next_time <= progress_time) {
            print_xfer_stats (progress_time);
            next_time += XTIME_PRECISION;
        }
    }
}

static ssize_t perform_input_read_operation(idx_t *n_bytes_read_ptr) {
    if ((conversions_mask & C_SYNC) && (conversions_mask & C_NOERROR)) {
        memset (ibuf, get_padding_char(), input_blocksize);
    }

    size_t bytes_to_read = (r_partial + r_full >= max_records) ? max_bytes : input_blocksize;
    ssize_t nread_val = iread_fnc (STDIN_FILENO, ibuf, bytes_to_read);

    if (nread_val > 0) {
        advance_input_offset (nread_val);
        if (i_nocache) {
            invalidate_cache (STDIN_FILENO, nread_val);
        }
    } else if (nread_val == 0) {
        i_nocache_eof |= i_nocache;
        o_nocache_eof |= o_nocache && ! (conversions_mask & C_NOTRUNC);
    }
    *n_bytes_read_ptr = nread_val;
    return nread_val;
}

typedef enum {
    READ_ACTION_BREAK,
    READ_ACTION_CONTINUE,
    READ_ACTION_PROCESS_ZERO
} ReadErrorAction;

static ReadErrorAction handle_read_error_recovery(ssize_t *nread_ptr, idx_t partread_val, int *exit_status_ptr) {
    if (!((conversions_mask & C_NOERROR) && status_level == STATUS_NONE)) {
        diagnose (errno, _("error reading %s"), quoteaf (input_file));
    }

    if (conversions_mask & C_NOERROR) {
        print_stats ();
        idx_t bad_portion = input_blocksize - partread_val;

        invalidate_cache (STDIN_FILENO, bad_portion);

        if (!advance_input_after_read_error (bad_portion)) {
            *exit_status_ptr = EXIT_FAILURE;
            input_seekable = false;
            input_seek_errno = ESPIPE;
            return READ_ACTION_BREAK;
        }
        if ((conversions_mask & C_SYNC) && !partread_val) {
            *nread_ptr = 0;
            return READ_ACTION_PROCESS_ZERO;
        } else {
            return READ_ACTION_CONTINUE;
        }
    } else {
        *exit_status_ptr = EXIT_FAILURE;
        return READ_ACTION_BREAK;
    }
}

static bool process_data_block_logic(ssize_t *n_bytes_read_ptr, idx_t *partread_ptr, int *saved_byte_ptr, int *exit_status_ptr) {
    idx_t n_bytes_current_block = *n_bytes_read_ptr;

    if (n_bytes_current_block < input_blocksize) {
        r_partial++;
        *partread_ptr = n_bytes_current_block;
        if (conversions_mask & C_SYNC) {
            if (!(conversions_mask & C_NOERROR)) {
                memset (ibuf + n_bytes_current_block,
                        get_padding_char(),
                        input_blocksize - n_bytes_current_block);
            }
            n_bytes_current_block = input_blocksize;
        }
    } else {
        r_full++;
        *partread_ptr = 0;
    }
    *n_bytes_read_ptr = n_bytes_current_block;

    if (!(conversions_mask & C_TWOBUFS)) {
        idx_t nwritten = iwrite (STDOUT_FILENO, obuf, n_bytes_current_block);
        w_bytes += nwritten;
        if (nwritten != n_bytes_current_block) {
            diagnose (errno, _("error writing %s"), quoteaf (output_file));
            *exit_status_ptr = EXIT_FAILURE;
            return false;
        } else if (n_bytes_current_block == input_blocksize) {
            w_full++;
        } else {
            w_partial++;
        }
        return true;
    }

    char *bufstart;
    idx_t processed_bytes = n_bytes_current_block;

    if (translation_needed) {
        translate_buffer (ibuf, processed_bytes);
    }

    if (conversions_mask & C_SWAB) {
        bufstart = swab_buffer (ibuf, &processed_bytes, saved_byte_ptr);
    } else {
        bufstart = ibuf;
    }

    if (conversions_mask & C_BLOCK) {
        copy_with_block (bufstart, processed_bytes);
    } else if (conversions_mask & C_UNBLOCK) {
        copy_with_unblock (bufstart, processed_bytes);
    } else {
        copy_simple (bufstart, processed_bytes);
    }
    return true;
}

static inline void finalize_swab_byte_phase(int saved_byte_val) {
    if (0 <= saved_byte_val) {
        char saved_char = saved_byte_val;
        if (conversions_mask & C_BLOCK) {
            copy_with_block (&saved_char, 1);
        } else if (conversions_mask & C_UNBLOCK) {
            copy_with_unblock (&saved_char, 1);
        } else {
            output_char (saved_char);
        }
    }
}

static inline void finalize_block_unblock_padding_phase(void) {
    if ((conversions_mask & C_BLOCK) && col > 0) {
        for (idx_t i = col; i < conversion_blocksize; i++) {
            output_char (space_character);
        }
    }

    if (col && (conversions_mask & C_UNBLOCK)) {
        output_char (newline_character);
    }
}

static bool finalize_remaining_output_buffer_phase(int *exit_status_ptr) {
    if (oc != 0) {
        idx_t nwritten = iwrite (STDOUT_FILENO, obuf, oc);
        w_bytes += nwritten;
        if (nwritten != 0) {
            w_partial++;
        }
        if (nwritten != oc) {
            diagnose (errno, _("error writing %s"), quoteaf (output_file));
            *exit_status_ptr = EXIT_FAILURE;
            return false;
        }
    }
    return true;
}

static bool finalize_truncate_if_needed_phase(int *exit_status_ptr) {
    if (!final_op_was_seek) {
        return true;
    }

    struct stat stdout_stat;
    if (ifstat (STDOUT_FILENO, &stdout_stat) != 0) {
        diagnose (errno, _("cannot fstat %s"), quoteaf (output_file));
        *exit_status_ptr = EXIT_FAILURE;
        return false;
    }

    if (S_ISREG (stdout_stat.st_mode) || S_TYPEISSHM (&stdout_stat)) {
        off_t output_offset = lseek (STDOUT_FILENO, 0, SEEK_CUR);
        if (0 <= output_offset && stdout_stat.st_size < output_offset) {
            if (iftruncate (STDOUT_FILENO, output_offset) != 0) {
                diagnose (errno, _("failed to truncate to %jd bytes"
                                   " in output file %s"),
                          (intmax_t) output_offset, quoteaf (output_file));
                *exit_status_ptr = EXIT_FAILURE;
                return false;
            }
        }
    }
    return true;
}

static inline void finalize_fsync_fdatasync_phase(void) {
    if ((conversions_mask & (C_FDATASYNC | C_FSYNC))
        && status_level == STATUS_PROGRESS
        && 0 <= reported_w_bytes && reported_w_bytes < w_bytes) {
        print_xfer_stats (0);
    }
}

static int
dd_copy (void)
{
  int exit_status = EXIT_SUCCESS;
  idx_t partread = 0;
  int saved_byte = -1;

  if (!handle_initial_skipping_input_phase(&exit_status)) {
    return exit_status;
  }

  if (!handle_initial_seeking_output_phase(&exit_status)) {
    return exit_status;
  }

  if (max_records == 0 && max_bytes == 0) {
    return exit_status;
  }

  alloc_ibuf ();
  alloc_obuf ();

  while (should_continue_copying_loop()) {
    check_and_print_progress();

    ssize_t nread_val;
    if (perform_input_read_operation(&nread_val) == 0) {
      break;
    } else if (nread_val < 0) {
        ReadErrorAction action = handle_read_error_recovery(&nread_val, partread, &exit_status);
        if (action == READ_ACTION_BREAK) {
            break;
        } else if (action == READ_ACTION_CONTINUE) {
            continue;
        }
        // If action is READ_ACTION_PROCESS_ZERO, nread_val is set to 0, and
        // the flow continues to process_data_block_logic.
    }

    if (!process_data_block_logic(&nread_val, &partread, &saved_byte, &exit_status)) {
      break;
    }
  }

  finalize_swab_byte_phase(saved_byte);
  finalize_block_unblock_padding_phase();

  if (!finalize_remaining_output_buffer_phase(&exit_status)) {
    return exit_status;
  }

  if (!finalize_truncate_if_needed_phase(&exit_status)) {
    return exit_status;
  }

  finalize_fsync_fdatasync_phase();

  return exit_status;
}

/* Synchronize output according to conversions_mask.
   Do this even if w_bytes is zero, as fsync and fdatasync
   flush out write requests from other processes too.
   Clear bits in conversions_mask so that synchronization is done only once.
   Return zero if successful, an exit status otherwise.  */

static int
synchronize_output (void)
{
  int current_exit_status = 0;
  int original_mask_flags = conversions_mask;
  bool fdatasync_attempted = (original_mask_flags & C_FDATASYNC) != 0;
  bool fsync_requested_originally = (original_mask_flags & C_FSYNC) != 0;

  conversions_mask &= ~ (C_FDATASYNC | C_FSYNC);

  bool fallback_to_fsync_needed = false;

  if (fdatasync_attempted)
    {
      if (ifdatasync (STDOUT_FILENO) != 0)
        {
          if (errno != ENOSYS && errno != EINVAL)
            {
              diagnose (errno, _("fdatasync failed for %s"), quoteaf (output_file));
              current_exit_status = EXIT_FAILURE;
            }
          fallback_to_fsync_needed = true;
        }
    }

  if (fsync_requested_originally || fallback_to_fsync_needed)
    {
      if (ifsync (STDOUT_FILENO) != 0)
        {
          diagnose (errno, _("fsync failed for %s"), quoteaf (output_file));
          return EXIT_FAILURE;
        }
    }

  return current_exit_status;
}

static void handle_ftruncate_error(int fd, off_t target_size, const char *filename, int *exit_status_ptr) {
  int ftruncate_errno = errno;
  struct stat st;
  if (ifstat(fd, &st) != 0) {
    diagnose(errno, _("cannot fstat %s"), quoteaf(filename));
    *exit_status_ptr = EXIT_FAILURE;
  } else if (S_ISREG(st.st_mode) || S_ISDIR(st.st_mode) || S_TYPEISSHM(&st)) {
    diagnose(ftruncate_errno, _("failed to truncate to %jd bytes" " in output file %s"), (intmax_t)target_size, quoteaf(filename));
    *exit_status_ptr = EXIT_FAILURE;
  }
}

static void invalidate_and_report_cache(int fd, const char *filename, bool condition_to_invalidate, int *exit_status_ptr) {
  if (condition_to_invalidate) {
    if (!invalidate_cache(fd, 0)) {
      diagnose(errno, _("failed to discard cache for: %s"), quotef(filename));
      *exit_status_ptr = EXIT_FAILURE;
    }
  }
}

int
main (int argc, char **argv)
{
  int i;
  int exit_status;
  off_t offset;

  install_signal_handlers ();

  initialize_main (&argc, &argv);
  set_program_name (argv[0]);
  setlocale (LC_ALL, "");
  bindtextdomain (PACKAGE, LOCALEDIR);
  textdomain (PACKAGE);

  atexit (maybe_close_stdout);

  page_size = getpagesize ();

  parse_gnu_standard_options_only (argc, argv, PROGRAM_NAME, PACKAGE, Version,
                                   true, usage, AUTHORS,
                                   (char const *) nullptr);
  close_stdout_required = false;

  for (i = 0; i < 256; i++)
    trans_table[i] = i;

  scanargs (argc, argv);

  apply_translations ();

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

  offset = lseek (STDIN_FILENO, 0, SEEK_CUR);
  input_seekable = (0 <= offset);
  input_offset = MAX (0, offset);
  input_seek_errno = errno;

  if (output_file == nullptr)
    {
      output_file = _("standard output");
      set_fd_flags (STDOUT_FILENO, output_flags, output_file);
    }
  else
    {
      mode_t perms = MODE_RW_UGO;
      int opts
        = (output_flags
           | (conversions_mask & C_NOCREAT ? 0 : O_CREAT)
           | (conversions_mask & C_EXCL ? O_EXCL : 0)
           | (seek_records || (conversions_mask & C_NOTRUNC) ? 0 : O_TRUNC));

      off_t target_output_size;
      if ((ckd_mul (&target_output_size, seek_records, output_blocksize)
           || ckd_add (&target_output_size, seek_bytes, target_output_size))
          && !(conversions_mask & C_NOTRUNC))
        error (EXIT_FAILURE, 0,
               _("offset too large: "
                 "cannot truncate to a length of seek=%jd"
                 " (%td-byte) blocks"),
               seek_records, output_blocksize);

      bool output_file_opened = false;
      if (seek_records)
        {
          if (ifd_reopen (STDOUT_FILENO, output_file, O_RDWR | opts, perms) == 0)
            output_file_opened = true;
          else
            {
              if (ifd_reopen (STDOUT_FILENO, output_file, O_WRONLY | opts, perms) == 0)
                output_file_opened = true;
            }
        }
      else
        {
          if (ifd_reopen (STDOUT_FILENO, output_file, O_WRONLY | opts, perms) == 0)
            output_file_opened = true;
        }

      if (!output_file_opened)
        error (EXIT_FAILURE, errno, _("failed to open %s"),
               quoteaf (output_file));

      if (seek_records != 0 && !(conversions_mask & C_NOTRUNC))
        {
          if (iftruncate (STDOUT_FILENO, target_output_size) != 0)
            {
              handle_ftruncate_error(STDOUT_FILENO, target_output_size, output_file, &exit_status);
            }
        }
    }

  start_time = gethrxtime ();
  next_time = start_time + XTIME_PRECISION;

  exit_status = dd_copy ();

  int sync_status = synchronize_output ();
  if (sync_status)
    exit_status = sync_status;

  if (max_records == 0 && max_bytes == 0)
    {
      invalidate_and_report_cache(STDIN_FILENO, input_file, i_nocache, &exit_status);
      invalidate_and_report_cache(STDOUT_FILENO, output_file, o_nocache, &exit_status);
    }
  else
    {
      invalidate_and_report_cache(STDIN_FILENO, input_file, (i_nocache || i_nocache_eof), &exit_status);
      invalidate_and_report_cache(STDOUT_FILENO, output_file, (o_nocache || o_nocache_eof), &exit_status);
    }

  finish_up ();
  main_exit (exit_status);
}
