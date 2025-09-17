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
    close_stdout ();
  else if (close_stream (stderr) != 0)
    _exit (EXIT_FAILURE);
}

/* Like the 'error' function but handle any pending newline,
   and do not exit.  */

ATTRIBUTE_FORMAT ((__printf__, 2, 3))
static void
diagnose (int errnum, char const *fmt, ...)
{
  if (0 < progress_len)
    {
      fputc ('\n', stderr);
      progress_len = 0;
    }

  va_list ap;
  va_start (ap, fmt);
  verror (0, errnum, fmt, ap);
  va_end (ap);
}

void print_usage_header(void)
{
    printf(_("Usage: %s [OPERAND]...\n  or:  %s OPTION\n"),
           program_name, program_name);
    fputs(_("Copy a file, converting and formatting according to the operands.\n\n"), stdout);
}

void print_basic_operands(void)
{
    fputs(_("\
  bs=BYTES        read and write up to BYTES bytes at a time (default: 512);\n\
                  overrides ibs and obs\n\
  cbs=BYTES       convert BYTES bytes at a time\n\
  conv=CONVS      convert the file as per the comma separated symbol list\n\
  count=N         copy only N input blocks\n\
  ibs=BYTES       read up to BYTES bytes at a time (default: 512)\n"), stdout);
}

void print_io_operands(void)
{
    fputs(_("\
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
                  'progress' shows periodic transfer statistics\n"), stdout);
}

void print_multipliers(void)
{
    fputs(_("\n\
N and BYTES may be followed by the following multiplicative suffixes:\n\
c=1, w=2, b=512, kB=1000, K=1024, MB=1000*1000, M=1024*1024, xM=M,\n\
GB=1000*1000*1000, G=1024*1024*1024, and so on for T, P, E, Z, Y, R, Q.\n\
Binary prefixes can be used, too: KiB=K, MiB=M, and so on.\n\
If N ends in 'B', it counts bytes not blocks.\n\n\
Each CONV symbol may be:\n\n"), stdout);
}

void print_conv_symbols(void)
{
    fputs(_("\
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
            with block or unblock, pad with spaces rather than NULs\n"), stdout);
    
    fputs(_("\
  excl      fail if the output file already exists\n\
  nocreat   do not create the output file\n\
  notrunc   do not truncate the output file\n\
  noerror   continue after read errors\n\
  fdatasync  physically write output file data before finishing\n\
  fsync     likewise, but also write metadata\n"), stdout);
}

void print_flag_if_defined(int flag, const char *message)
{
    if (flag)
        fputs(_(message), stdout);
}

void print_flag_symbols(void)
{
    fputs(_("\nEach FLAG symbol may be:\n\n  append    append mode (makes sense only for output; conv=notrunc suggested)\n"), stdout);
    
    print_flag_if_defined(O_CIO, "  cio       use concurrent I/O for data\n");
    print_flag_if_defined(O_DIRECT, "  direct    use direct I/O for data\n");
    
    fputs(_("  directory  fail unless a directory\n"), stdout);
    
    print_flag_if_defined(O_DSYNC, "  dsync     use synchronized I/O for data\n");
    print_flag_if_defined(O_SYNC, "  sync      likewise, but also for metadata\n");
    
    fputs(_("  fullblock  accumulate full blocks of input (iflag only)\n"), stdout);
    
    print_flag_if_defined(O_NONBLOCK, "  nonblock  use non-blocking I/O\n");
    print_flag_if_defined(O_NOATIME, "  noatime   do not update access time\n");
    
#if HAVE_POSIX_FADVISE
    print_flag_if_defined(O_NOCACHE, "  nocache   Request to drop cache.  See also oflag=sync\n");
#endif
    
    print_flag_if_defined(O_NOCTTY, "  noctty    do not assign controlling terminal from file\n");
    print_flag_if_defined(HAVE_WORKING_O_NOFOLLOW, "  nofollow  do not follow symlinks\n");
    print_flag_if_defined(O_NOLINKS, "  nolinks   fail if multiply-linked\n");
    print_flag_if_defined(O_BINARY, "  binary    use binary I/O for data\n");
    print_flag_if_defined(O_TEXT, "  text      use text I/O for data\n");
}

void print_signal_info(void)
{
    const char *signal_name = (SIGINFO == SIGUSR1) ? "USR1" : "INFO";
    printf(_("\nSending a %s signal to a running 'dd' process makes it\n\
print I/O statistics to standard error and then resume copying.\n\n\
Options are:\n\n"), signal_name);
}

void print_help_details(void)
{
    print_usage_header();
    print_basic_operands();
    print_io_operands();
    print_multipliers();
    print_conv_symbols();
    print_flag_symbols();
    print_signal_info();
    fputs(HELP_OPTION_DESCRIPTION, stdout);
    fputs(VERSION_OPTION_DESCRIPTION, stdout);
    emit_ancillary_info(PROGRAM_NAME);
}

void usage(int status)
{
    if (status != EXIT_SUCCESS)
        emit_try_help();
    else
        print_help_details();
    
    exit(status);
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

  bool extra_byte_for_swab = !!(conversions_mask & C_SWAB);
  ibuf = alignalloc (page_size, input_blocksize + extra_byte_for_swab);
  if (!ibuf)
    handle_allocation_failure();
}

static void
handle_allocation_failure (void)
{
  char hbuf[LONGEST_HUMAN_READABLE + 1];
  error (EXIT_FAILURE, 0,
         _("memory exhausted by input buffer of size %td bytes (%s)"),
         input_blocksize,
         human_readable (input_blocksize, hbuf,
                         human_opts | human_base_1024, 1, 1));
}

/* Ensure output buffer OBUF is allocated/initialized.  */

static void
alloc_obuf (void)
{
  if (obuf)
    return;

  if (conversions_mask & C_TWOBUFS)
    {
      allocate_output_buffer();
    }
  else
    {
      alloc_ibuf();
      obuf = ibuf;
    }
}

static void
allocate_output_buffer (void)
{
  obuf = alignalloc(page_size, output_blocksize);
  if (!obuf)
    {
      report_memory_exhaustion_error();
    }
}

static void
report_memory_exhaustion_error (void)
{
  char hbuf[LONGEST_HUMAN_READABLE + 1];
  error(EXIT_FAILURE, 0,
        _("memory exhausted by output buffer of size %td bytes (%s)"),
        output_blocksize,
        human_readable(output_blocksize, hbuf,
                      human_opts | human_base_1024, 1, 1));
}

static void
translate_charset (char const *new_trans)
{
  for (int i = 0; i < 256; i++)
    trans_table[i] = new_trans[trans_table[i]];
  translation_needed = true;
}

/* Return true if I has more than one bit set.  I must be nonnegative.  */

static inline bool
multiple_bits_set (int i)
{
  return MULTIPLE_BITS_SET (i);
}

static bool
abbreviation_lacks_prefix(char const *message)
{
  size_t len = strlen(message);
  if (len < 2) {
    return false;
  }
  return message[len - 2] == ' ';
}

/* Print transfer statistics.  */

static xtime_t get_current_time(xtime_t progress_time)
{
    return progress_time ? progress_time : gethrxtime();
}

static void calculate_transfer_rate(xtime_t start_time, xtime_t now, 
                                   char *bpsbuf, int bpsbufsize,
                                   double *delta_s, char const **bytes_per_second)
{
    static char const slash_s[] = "/s";
    
    if (start_time < now)
    {
        double XTIME_PRECISIONe0 = XTIME_PRECISION;
        xtime_t delta_xtime = now - start_time;
        *delta_s = delta_xtime / XTIME_PRECISIONe0;
        *bytes_per_second = human_readable(w_bytes, bpsbuf, human_opts,
                                          XTIME_PRECISION, delta_xtime);
        strcat(*bytes_per_second - bpsbuf + bpsbuf, slash_s);
    }
    else
    {
        *delta_s = 0;
        snprintf(bpsbuf, bpsbufsize, "%s B/s", _("Infinity"));
        *bytes_per_second = bpsbuf;
    }
}

static void format_delta_time(char *delta_s_buf, size_t buf_size, 
                             double delta_s, xtime_t progress_time)
{
    const char *format = progress_time ? "%.0f s" : "%g s";
    snprintf(delta_s_buf, buf_size, format, delta_s);
}

static int print_stats_message(char const *si, char const *iec, 
                               char const *delta_s_buf, char const *bytes_per_second)
{
    if (abbreviation_lacks_prefix(si))
    {
        return fprintf(stderr,
                      ngettext("%jd byte copied, %s, %s",
                              "%jd bytes copied, %s, %s",
                              select_plural(w_bytes)),
                      w_bytes, delta_s_buf, bytes_per_second);
    }
    
    if (abbreviation_lacks_prefix(iec))
    {
        return fprintf(stderr,
                      _("%jd bytes (%s) copied, %s, %s"),
                      w_bytes, si, delta_s_buf, bytes_per_second);
    }
    
    return fprintf(stderr,
                  _("%jd bytes (%s, %s) copied, %s, %s"),
                  w_bytes, si, iec, delta_s_buf, bytes_per_second);
}

static void handle_progress_output(xtime_t progress_time, int stats_len)
{
    if (!progress_time)
    {
        fputc('\n', stderr);
        return;
    }
    
    if (0 <= stats_len && stats_len < progress_len)
    {
        fprintf(stderr, "%*s", progress_len - stats_len, "");
    }
    progress_len = stats_len;
}

static void print_xfer_stats(xtime_t progress_time)
{
    static char const slash_s[] = "/s";
    char hbuf[3][LONGEST_HUMAN_READABLE + sizeof slash_s];
    double delta_s;
    char const *bytes_per_second;
    char delta_s_buf[24];
    
    xtime_t now = get_current_time(progress_time);
    
    char const *si = human_readable(w_bytes, hbuf[0], human_opts, 1, 1);
    char const *iec = human_readable(w_bytes, hbuf[1],
                                     human_opts | human_base_1024, 1, 1);
    
    calculate_transfer_rate(start_time, now, hbuf[2], sizeof hbuf[2],
                          &delta_s, &bytes_per_second);
    
    if (progress_time)
    {
        fputc('\r', stderr);
    }
    
    format_delta_time(delta_s_buf, sizeof delta_s_buf, delta_s, progress_time);
    
    int stats_len = print_stats_message(si, iec, delta_s_buf, bytes_per_second);
    
    handle_progress_output(progress_time, stats_len);
    
    reported_w_bytes = w_bytes;
}

static void print_newline_if_progress(void)
{
    if (0 < progress_len)
    {
        fputc('\n', stderr);
        progress_len = 0;
    }
}

static void print_record_counts(void)
{
    fprintf(stderr,
            _("%jd+%jd records in\n"
              "%jd+%jd records out\n"),
            r_full, r_partial, w_full, w_partial);
}

static void print_truncated_records(void)
{
    if (r_truncate != 0)
    {
        fprintf(stderr,
                ngettext("%jd truncated record\n",
                         "%jd truncated records\n",
                         select_plural(r_truncate)),
                r_truncate);
    }
}

static void print_stats(void)
{
    if (status_level == STATUS_NONE)
        return;

    print_newline_if_progress();
    print_record_counts();
    print_truncated_records();

    if (status_level == STATUS_NOXFER)
        return;

    print_xfer_stats(0);
}

/* An ordinary signal was received; arrange for the program to exit.  */

static void interrupt_handler(int sig)
{
    if (!SA_RESETHAND)
    {
        signal(sig, SIG_DFL);
    }
    interrupt_signal = sig;
}

/* An info signal was received; arrange for the program to print status.  */

static void
siginfo_handler (int sig)
{
  if (! SA_NOCLDSTOP)
    signal (sig, siginfo_handler);
  info_signal_count++;
}

/* Install the signal handlers.  */

static bool should_catch_siginfo(void)
{
    return !(SIGINFO == SIGUSR1 && getenv("POSIXLY_CORRECT"));
}

#if SA_NOCLDSTOP
static void setup_signal_set(sigset_t *signals, bool catch_siginfo)
{
    struct sigaction act;
    
    sigemptyset(signals);
    
    if (catch_siginfo)
        sigaddset(signals, SIGINFO);
    
    sigaction(SIGINT, nullptr, &act);
    if (act.sa_handler != SIG_IGN)
        sigaddset(signals, SIGINT);
}

static void install_siginfo_handler(sigset_t *signals)
{
    struct sigaction act;
    
    if (!sigismember(signals, SIGINFO))
        return;
    
    act.sa_handler = siginfo_handler;
    act.sa_flags = 0;
    act.sa_mask = *signals;
    sigaction(SIGINFO, &act, nullptr);
}

static void install_sigint_handler(sigset_t *signals)
{
    struct sigaction act;
    
    if (!sigismember(signals, SIGINT))
        return;
    
    act.sa_handler = interrupt_handler;
    act.sa_flags = SA_NODEFER | SA_RESETHAND;
    act.sa_mask = *signals;
    sigaction(SIGINT, &act, nullptr);
}

static void install_signal_handlers_posix(bool catch_siginfo)
{
    setup_signal_set(&caught_signals, catch_siginfo);
    install_siginfo_handler(&caught_signals);
    install_sigint_handler(&caught_signals);
}
#else
static void install_siginfo_handler_legacy(bool catch_siginfo)
{
    if (!catch_siginfo)
        return;
    
    signal(SIGINFO, siginfo_handler);
    siginterrupt(SIGINFO, 1);
}

static void install_sigint_handler_legacy(void)
{
    if (signal(SIGINT, SIG_IGN) == SIG_IGN)
        return;
    
    signal(SIGINT, interrupt_handler);
    siginterrupt(SIGINT, 1);
}

static void install_signal_handlers_legacy(bool catch_siginfo)
{
    install_siginfo_handler_legacy(catch_siginfo);
    install_sigint_handler_legacy();
}
#endif

static void install_signal_handlers(void)
{
    bool catch_siginfo = should_catch_siginfo();
    
#if SA_NOCLDSTOP
    install_signal_handlers_posix(catch_siginfo);
#else
    install_signal_handlers_legacy(catch_siginfo);
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
  while (close (fd) != 0)
    {
      if (errno != EINTR)
        return -1;
      if (errno == EBADF)
        break;
    }

  return 0;
}

static int synchronize_output (void);

static void handle_sync_status(void)
{
    int sync_status = synchronize_output();
    if (sync_status)
        exit(sync_status);
}

static void close_file_descriptor(int fd, const char *file_description, const char *file_name)
{
    if (iclose(fd) != 0)
        error(EXIT_FAILURE, errno, file_description, quoteaf(file_name));
}

static void cleanup(void)
{
    if (!interrupt_signal)
    {
        handle_sync_status();
    }

    close_file_descriptor(STDIN_FILENO, _("closing input file %s"), input_file);
    close_file_descriptor(STDOUT_FILENO, _("closing output file %s"), output_file);
}

/* Process any pending signals.  If signals are caught, this function
   should be called periodically.  Ideally there should never be an
   unbounded amount of time when signals are not being processed.  */

static void block_signals(sigset_t *oldset)
{
    sigprocmask(SIG_BLOCK, &caught_signals, oldset);
}

static void restore_signals(sigset_t *oldset)
{
    sigprocmask(SIG_SETMASK, oldset, nullptr);
}

static void get_signal_states(int *interrupt, int *infos)
{
    *interrupt = interrupt_signal;
    *infos = info_signal_count;
}

static void decrement_info_count(int infos)
{
    if (infos)
        info_signal_count = infos - 1;
}

static void handle_interrupt(int interrupt)
{
    if (interrupt)
    {
        cleanup();
        print_stats();
        raise(interrupt);
    }
    else
    {
        print_stats();
    }
}

static void process_signals(void)
{
    while (interrupt_signal || info_signal_count)
    {
        int interrupt;
        int infos;
        sigset_t oldset;

        block_signals(&oldset);
        get_signal_states(&interrupt, &infos);
        decrement_info_count(infos);
        restore_signals(&oldset);
        handle_interrupt(interrupt);
    }
}

static void finish_up(void)
{
    process_signals();
    cleanup();
    print_stats();
}

static void quit(int code)
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
    return *pending;

  intmax_t c_pending;
  if (ckd_add (&c_pending, *pending, len))
    c_pending = INTMAX_MAX;
    
  *pending = c_pending % IO_BUFSIZE;
  
  if (c_pending > *pending)
    return c_pending - *pending;
    
  return 0;
}

/* Discard the cache from the current offset of either
   STDIN_FILENO or STDOUT_FILENO.
   Return true on success.
   Return false on failure, with errno set.  */

static off_t get_input_offset(void)
{
    if (input_seekable)
        return input_offset;
    
    errno = ESPIPE;
    return -1;
}

static off_t get_output_offset(int fd, off_t clen, off_t pending, off_t len)
{
    static off_t output_offset = -2;
    
    if (output_offset == -1)
        return -1;
    
    if (output_offset < 0)
        output_offset = lseek(fd, 0, SEEK_CUR);
    else if (len)
        output_offset += clen + pending;
    
    return output_offset;
}

static off_t get_file_offset(int fd, off_t clen, off_t pending, off_t len)
{
    if (fd == STDIN_FILENO)
        return get_input_offset();
    
    return get_output_offset(fd, clen, pending, len);
}

static void adjust_cache_params(off_t *clen, off_t *pending, off_t len, bool nocache_eof)
{
    if (!len && *clen && nocache_eof)
    {
        *pending = *clen;
        *clen = 0;
    }
}

static off_t calculate_invalidation_offset(off_t offset, off_t clen, off_t pending)
{
    off_t result = offset - clen - pending;
    
    if (clen == 0)
        result -= result % page_size;
    
    return result;
}

static int perform_fadvise(int fd, off_t offset, off_t clen)
{
#if HAVE_POSIX_FADVISE
    return posix_fadvise(fd, offset, clen, POSIX_FADV_DONTNEED);
#else
    return ENOTSUP;
#endif
}

static bool should_skip_invalidation(off_t len, off_t clen, bool nocache_eof)
{
    if (len && !clen)
        return true;
    
    if (!len && !clen && !nocache_eof)
        return true;
    
    return false;
}

static bool invalidate_cache(int fd, off_t len)
{
    bool nocache_eof = (fd == STDIN_FILENO ? i_nocache_eof : o_nocache_eof);
    off_t clen = cache_round(fd, len);
    
    if (should_skip_invalidation(len, clen, nocache_eof))
        return true;
    
    off_t pending = len ? cache_round(fd, 0) : 0;
    off_t offset = get_file_offset(fd, clen, pending, len);
    
    if (offset < 0)
    {
        errno = (errno == 0) ? ESPIPE : errno;
        return false;
    }
    
    adjust_cache_params(&clen, &pending, len, nocache_eof);
    
    offset = calculate_invalidation_offset(offset, clen, pending);
    int adv_ret = perform_fadvise(fd, offset, clen);
    errno = adv_ret;
    
    return adv_ret == 0;
}

/* Read from FD into the buffer BUF of size SIZE, processing any
   signals that arrive before bytes are read.  Return the number of
   bytes read if successful, -1 (setting errno) on failure.  */

static ssize_t
iread (int fd, char *buf, idx_t size)
{
  ssize_t nread;
  static ssize_t prev_nread;

  nread = perform_read_with_retry(fd, buf, size, prev_nread);
  
  handle_short_read(nread, size);
  
  check_and_warn_partial_read(nread, size, prev_nread);

  prev_nread = nread;
  return nread;
}

static ssize_t
perform_read_with_retry(int fd, char *buf, idx_t size, ssize_t prev_nread)
{
  ssize_t nread;
  
  do
    {
      process_signals ();
      nread = read (fd, buf, size);
      
      if (should_ignore_direct_io_error(nread, prev_nread, size))
        {
          errno = 0;
          nread = 0;
        }
    }
  while (nread < 0 && errno == EINTR);
  
  return nread;
}

static int
should_ignore_direct_io_error(ssize_t nread, ssize_t prev_nread, idx_t size)
{
  return nread == -1 && errno == EINVAL
         && 0 < prev_nread && prev_nread < size
         && (input_flags & O_DIRECT);
}

static void
handle_short_read(ssize_t nread, idx_t size)
{
  if (0 < nread && nread < size)
    process_signals ();
}

static void
check_and_warn_partial_read(ssize_t nread, idx_t size, ssize_t prev_nread)
{
  if (0 < nread && warn_partial_read)
    {
      if (0 < prev_nread && prev_nread < size)
        {
          issue_partial_read_warning(prev_nread);
          warn_partial_read = false;
        }
    }
}

static void
issue_partial_read_warning(idx_t prev)
{
  if (status_level != STATUS_NONE)
    diagnose (0, ngettext (("warning: partial read (%td byte); "
                            "suggest iflag=fullblock"),
                           ("warning: partial read (%td bytes); "
                            "suggest iflag=fullblock"),
                           select_plural (prev)),
              prev);
}

/* Wrapper around iread function to accumulate full blocks.  */
static ssize_t
iread_fullblock (int fd, char *buf, idx_t size)
{
  ssize_t nread = 0;

  while (0 < size)
    {
      ssize_t ncurr = iread (fd, buf, size);
      if (ncurr < 0)
        return ncurr;
      if (ncurr == 0)
        break;
      nread += ncurr;
      buf   += ncurr;
      size  -= ncurr;
    }

  return nread;
}

/* Write to FD the buffer BUF of size SIZE, processing any signals
   that arrive.  Return the number of bytes written, setting errno if
   this is less than SIZE.  Keep trying if there are partial
   writes.  */

static void handle_direct_output_disable(void)
{
    int old_flags = fcntl(STDOUT_FILENO, F_GETFL);
    if (fcntl(STDOUT_FILENO, F_SETFL, old_flags & ~O_DIRECT) != 0
        && status_level != STATUS_NONE)
        diagnose(errno, _("failed to turn off O_DIRECT: %s"),
                quotef(output_file));

    o_nocache_eof = true;
    invalidate_cache(STDOUT_FILENO, 0);
    conversions_mask |= C_FSYNC;
}

static bool should_disable_direct_output(idx_t size)
{
    return (output_flags & O_DIRECT) && size < output_blocksize;
}

static ssize_t perform_sparse_seek(int fd, char const *buf, idx_t size)
{
    if (!(conversions_mask & C_SPARSE) || !is_nul(buf, size))
        return 0;

    if (lseek(fd, size, SEEK_CUR) < 0)
    {
        conversions_mask &= ~C_SPARSE;
        return 0;
    }

    final_op_was_seek = true;
    return size;
}

static ssize_t write_block(int fd, char const *buf, idx_t offset, idx_t remaining)
{
    process_signals();
    final_op_was_seek = false;

    ssize_t nwritten = perform_sparse_seek(fd, buf + offset, remaining);
    
    if (!nwritten)
        nwritten = write(fd, buf + offset, remaining);

    return nwritten;
}

static bool handle_write_error(ssize_t nwritten)
{
    if (nwritten < 0)
    {
        return errno == EINTR;
    }
    
    if (nwritten == 0)
    {
        errno = ENOSPC;
        return false;
    }
    
    return true;
}

static idx_t
iwrite(int fd, char const *buf, idx_t size)
{
    idx_t total_written = 0;

    if (should_disable_direct_output(size))
        handle_direct_output_disable();

    while (total_written < size)
    {
        ssize_t nwritten = write_block(fd, buf, total_written, size - total_written);
        
        if (!handle_write_error(nwritten))
            break;
            
        if (nwritten > 0)
            total_written += nwritten;
    }

    if (o_nocache && total_written)
        invalidate_cache(fd, total_written);

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
      handle_incomplete_write(nwritten);
    }
  else
    {
      w_full++;
      oc = 0;
    }
}

static void
handle_incomplete_write(idx_t nwritten)
{
  diagnose (errno, _("writing to %s"), quoteaf (output_file));
  if (nwritten != 0)
    w_partial++;
  quit (EXIT_FAILURE);
}

/* Restart on EINTR from fdatasync.  */

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

  do
    {
      process_signals ();
      ret = fd_reopen (desired_fd, file, flag, mode);
    }
  while (ret < 0 && errno == EINTR);

  return ret;
}

/* Restart on EINTR from fstat.  */

static int
ifstat (int fd, struct stat *st)
{
  int ret;

  do
    {
      process_signals ();
      ret = fstat (fd, st);
    }
  while (ret < 0 && errno == EINTR);

  return ret;
}

/* Restart on EINTR from fsync.  */

static int
ifsync (int fd)
{
  int ret;

  do
    {
      process_signals ();
      ret = fsync (fd);
    }
  while (ret < 0 && errno == EINTR);

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
  while (ret < 0 && errno == EINTR);

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

static struct symbol_value const *
find_symbol_entry(char const *str, struct symbol_value const *table)
{
    for (struct symbol_value const *entry = table; entry->symbol[0]; entry++)
    {
        if (operand_matches(str, entry->symbol, ',') && entry->value)
            return entry;
    }
    return NULL;
}

static void
report_invalid_symbol(char const *str, char const *strcomma, char const *error_msgid)
{
    idx_t slen = strcomma ? strcomma - str : strlen(str);
    diagnose(0, "%s: %s", _(error_msgid),
            quotearg_n_style_mem(0, locale_quoting_style, str, slen));
    usage(EXIT_FAILURE);
}

static int
update_value(int current_value, int entry_value, bool exclusive)
{
    return exclusive ? entry_value : (current_value | entry_value);
}

static char const *
get_next_token(char const *str)
{
    char const *strcomma = strchr(str, ',');
    return strcomma ? strcomma + 1 : NULL;
}

static int
parse_symbols(char const *str, struct symbol_value const *table,
              bool exclusive, char const *error_msgid)
{
    int value = 0;
    char const *current_str = str;

    while (current_str)
    {
        char const *strcomma = strchr(current_str, ',');
        struct symbol_value const *entry = find_symbol_entry(current_str, table);

        if (!entry)
            report_invalid_symbol(current_str, strcomma, error_msgid);

        value = update_value(value, entry->value, exclusive);
        current_str = get_next_token(current_str);
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
  int indeterminate = 0;
  uintmax_t n = indeterminate;
  char *suffix;
  static char const suffixes[] = "bcEGkKMPQRTwYZ0";
  strtol_error e = xstrtoumax (str, &suffix, 10, &n, suffixes);
  intmax_t result;

  e = handle_b_suffix(&suffix, str, e);
  
  if ((e & ~LONGINT_OVERFLOW) == LONGINT_INVALID_SUFFIX_CHAR && *suffix == 'x')
    {
      result = handle_multiplication(suffix, n, str, &e, indeterminate);
    }
  else
    {
      result = convert_to_intmax(n, &e);
    }

  *invalid = e;
  return result;
}

static strtol_error handle_b_suffix(char **suffix, char const *str, strtol_error e)
{
  if ((e & ~LONGINT_OVERFLOW) != LONGINT_INVALID_SUFFIX_CHAR)
    return e;
    
  if (*(*suffix) != 'B' || str >= *suffix || (*suffix)[-1] == 'B')
    return e;
    
  (*suffix)++;
  if (!*(*suffix))
    e &= ~LONGINT_INVALID_SUFFIX_CHAR;
    
  return e;
}

static intmax_t handle_multiplication(char *suffix, uintmax_t n, char const *str, 
                                      strtol_error *e, int indeterminate)
{
  strtol_error f = LONGINT_OK;
  intmax_t o = parse_integer(suffix + 1, &f);
  intmax_t result;
  
  if ((f & ~LONGINT_OVERFLOW) != LONGINT_OK)
    {
      *e = f;
      return indeterminate;
    }
  
  if (ckd_mul(&result, n, o) || (result != 0 && ((*e | f) & LONGINT_OVERFLOW)))
    {
      *e = LONGINT_OVERFLOW;
      return INTMAX_MAX;
    }
  
  check_zero_multiplier(result, str);
  *e = LONGINT_OK;
  return result;
}

static void check_zero_multiplier(intmax_t result, char const *str)
{
  if (result == 0 && STRPREFIX(str, "0x"))
    diagnose(0, _("warning: %s is a zero multiplier; use %s if that is intended"),
             quote_n(0, "0x"), quote_n(1, "00x"));
}

static intmax_t convert_to_intmax(uintmax_t n, strtol_error *e)
{
  if (n <= INTMAX_MAX)
    return n;
    
  *e = LONGINT_OVERFLOW;
  return INTMAX_MAX;
}

/* OPERAND is of the form "X=...".  Return true if X is NAME.  */

ATTRIBUTE_PURE
static bool
operand_is (char const *operand, char const *name)
{
  return operand_matches (operand, name, '=');
}

static void handle_invalid_operand(char const *name)
{
    diagnose (0, _("unrecognized operand %s"), quoteaf (name));
    usage (EXIT_FAILURE);
}

static void handle_invalid_number(strtol_error invalid, char const *val)
{
    if (invalid != LONGINT_OK)
        error (EXIT_FAILURE, invalid == LONGINT_OVERFLOW ? EOVERFLOW : 0,
               "%s: %s", _("invalid number"), quoteaf (val));
}

static idx_t get_max_blocksize(void)
{
    return MIN (IDX_MAX - 1, MIN (SSIZE_MAX, OFF_T_MAX));
}

static void process_file_operand(char const *name, char const *val)
{
    if (operand_is (name, "if"))
        input_file = val;
    else if (operand_is (name, "of"))
        output_file = val;
}

static bool process_flag_operand(char const *name, char const *val)
{
    if (operand_is (name, "conv"))
    {
        conversions_mask |= parse_symbols (val, conversions, false,
                                           N_("invalid conversion"));
        return true;
    }
    if (operand_is (name, "iflag"))
    {
        input_flags |= parse_symbols (val, flags, false,
                                      N_("invalid input flag"));
        return true;
    }
    if (operand_is (name, "oflag"))
    {
        output_flags |= parse_symbols (val, flags, false,
                                       N_("invalid output flag"));
        return true;
    }
    if (operand_is (name, "status"))
    {
        status_level = parse_symbols (val, statuses, true,
                                      N_("invalid status level"));
        return true;
    }
    return false;
}

static void set_blocksize_limits(char const *name, intmax_t *n_min, intmax_t *n_max, idx_t **converted_idx, idx_t *blocksize)
{
    idx_t max_blocksize = get_max_blocksize();
    
    if (operand_is (name, "ibs"))
    {
        *n_min = 1;
        *n_max = max_blocksize;
        *converted_idx = &input_blocksize;
    }
    else if (operand_is (name, "obs"))
    {
        *n_min = 1;
        *n_max = max_blocksize;
        *converted_idx = &output_blocksize;
    }
    else if (operand_is (name, "bs"))
    {
        *n_min = 1;
        *n_max = max_blocksize;
        *converted_idx = blocksize;
    }
    else if (operand_is (name, "cbs"))
    {
        *n_min = 1;
        *n_max = MIN (SIZE_MAX, IDX_MAX);
        *converted_idx = &conversion_blocksize;
    }
}

static bool process_numeric_operand(char const *name, intmax_t n, bool has_B, 
                                   intmax_t *skip, bool *skip_B,
                                   intmax_t *seek, bool *seek_B,
                                   intmax_t *count, bool *count_B)
{
    if (operand_is (name, "skip") || operand_is (name, "iseek"))
    {
        *skip = n;
        *skip_B = has_B;
        return true;
    }
    if (operand_is (name + (*name == 'o'), "seek"))
    {
        *seek = n;
        *seek_B = has_B;
        return true;
    }
    if (operand_is (name, "count"))
    {
        *count = n;
        *count_B = has_B;
        return true;
    }
    return false;
}

static void validate_number_range(intmax_t n, intmax_t n_min, intmax_t n_max, strtol_error *invalid)
{
    if (n < n_min)
        *invalid = LONGINT_INVALID;
    else if (n_max < n)
        *invalid = LONGINT_OVERFLOW;
}

static void apply_blocksize_settings(idx_t blocksize)
{
    #define DEFAULT_BLOCKSIZE 512
    
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

static void apply_skip_settings(intmax_t skip, bool skip_B)
{
    if (skip_B)
        input_flags |= O_SKIP_BYTES;
    if (input_flags & O_SKIP_BYTES && skip != 0)
    {
        skip_records = skip / input_blocksize;
        skip_bytes = skip % input_blocksize;
    }
    else if (skip != 0)
        skip_records = skip;
}

static void apply_count_settings(intmax_t count, bool count_B)
{
    if (count_B)
        input_flags |= O_COUNT_BYTES;
    if (input_flags & O_COUNT_BYTES && count != INTMAX_MAX)
    {
        max_records = count / input_blocksize;
        max_bytes = count % input_blocksize;
    }
    else if (count != INTMAX_MAX)
        max_records = count;
}

static void apply_seek_settings(intmax_t seek, bool seek_B)
{
    if (seek_B)
        output_flags |= O_SEEK_BYTES;
    if (output_flags & O_SEEK_BYTES && seek != 0)
    {
        seek_records = seek / output_blocksize;
        seek_bytes = seek % output_blocksize;
    }
    else if (seek != 0)
        seek_records = seek;
}

static void validate_flags(void)
{
    if (input_flags & (O_DSYNC | O_SYNC))
        input_flags |= O_RSYNC;

    if (output_flags & O_FULLBLOCK)
    {
        diagnose (0, "%s: %s", _("invalid output flag"), quote ("fullblock"));
        usage (EXIT_FAILURE);
    }
}

static void setup_read_function(void)
{
    warn_partial_read =
        (! (conversions_mask & C_TWOBUFS) && ! (input_flags & O_FULLBLOCK)
         && (skip_records
             || (0 < max_records && max_records < INTMAX_MAX)
             || (input_flags | output_flags) & O_DIRECT));

    iread_fnc = ((input_flags & O_FULLBLOCK)
                 ? iread_fullblock
                 : iread);
    input_flags &= ~O_FULLBLOCK;
}

static void validate_conversions(void)
{
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

static void setup_nocache_flags(void)
{
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

static void process_operand(char const *name, char const *val, idx_t *blocksize,
                           intmax_t *skip, bool *skip_B,
                           intmax_t *seek, bool *seek_B,
                           intmax_t *count, bool *count_B)
{
    process_file_operand(name, val);
    
    if (process_flag_operand(name, val))
        return;
    
    strtol_error invalid = LONGINT_OK;
    intmax_t n = parse_integer (val, &invalid);
    bool has_B = !!strchr (val, 'B');
    intmax_t n_min = 0;
    intmax_t n_max = INTMAX_MAX;
    idx_t *converted_idx = nullptr;
    
    set_blocksize_limits(name, &n_min, &n_max, &converted_idx, blocksize);
    
    if (!process_numeric_operand(name, n, has_B, skip, skip_B, seek, seek_B, count, count_B))
    {
        if (!converted_idx)
            handle_invalid_operand(name);
    }
    
    validate_number_range(n, n_min, n_max, &invalid);
    handle_invalid_number(invalid, val);
    
    if (converted_idx)
        *converted_idx = n;
}

static void scanargs (int argc, char *const *argv)
{
    idx_t blocksize = 0;
    intmax_t count = INTMAX_MAX;
    intmax_t skip = 0;
    intmax_t seek = 0;
    bool count_B = false, skip_B = false, seek_B = false;

    for (int i = optind; i < argc; i++)
    {
        char const *name = argv[i];
        char const *val = strchr (name, '=');

        if (val == nullptr)
            handle_invalid_operand(name);
        val++;

        process_operand(name, val, &blocksize, &skip, &skip_B, &seek, &seek_B, &count, &count_B);
    }

    apply_blocksize_settings(blocksize);
    validate_flags();
    apply_skip_settings(skip, skip_B);
    apply_count_settings(count, count_B);
    apply_seek_settings(seek, seek_B);
    setup_read_function();
    validate_conversions();
    setup_nocache_flags();
}

/* Fix up translation table. */

static void apply_case_conversion(int (*case_func)(int))
{
    int i;
    for (i = 0; i < 256; i++)
        trans_table[i] = case_func(trans_table[i]);
    translation_needed = true;
}

static void apply_charset_conversion(const unsigned char *charset)
{
    translate_charset(charset);
    newline_character = charset['\n'];
    space_character = charset[' '];
}

static void apply_ascii_conversion(void)
{
    if (conversions_mask & C_ASCII)
        translate_charset(ebcdic_to_ascii);
}

static void apply_case_conversions(void)
{
    if (conversions_mask & C_UCASE)
        apply_case_conversion(toupper);
    else if (conversions_mask & C_LCASE)
        apply_case_conversion(tolower);
}

static void apply_encoding_conversions(void)
{
    if (conversions_mask & C_EBCDIC)
        apply_charset_conversion(ascii_to_ebcdic);
    else if (conversions_mask & C_IBM)
        apply_charset_conversion(ascii_to_ibm);
}

static void apply_translations(void)
{
    apply_ascii_conversion();
    apply_case_conversions();
    apply_encoding_conversions();
}

/* Apply the character-set translations specified by the user
   to the NREAD bytes in BUF.  */

static void
translate_buffer (char *buf, idx_t nread)
{
  for (idx_t i = 0; i < nread; i++)
    buf[i] = trans_table[to_uchar (buf[i])];
}

/* Swap *NREAD bytes in BUF, which should have room for an extra byte
   after the end because the swapping is not in-place.  If *SAVED_BYTE
   is nonnegative, also swap that initial byte from the previous call.
   Save the last byte into into *SAVED_BYTE if needed to make the
   resulting *NREAD even, and set *SAVED_BYTE to -1 otherwise.
   Return the buffer's adjusted start, either BUF or BUF + 1.  */

static int should_save_byte(int prev_saved, idx_t nread)
{
    return (prev_saved < 0) == (nread & 1);
}

static void save_last_byte(char *buf, idx_t *nread, int *saved_byte)
{
    unsigned char c = buf[--*nread];
    *saved_byte = c;
}

static void swap_bytes(char *buf, idx_t nread)
{
    for (idx_t i = nread; 1 < i; i -= 2)
        buf[i] = buf[i - 2];
}

static char *adjust_buffer_start(char *buf, int prev_saved, idx_t *nread)
{
    if (prev_saved < 0)
        return buf + 1;
    
    buf[1] = prev_saved;
    ++*nread;
    return buf;
}

static char *
swab_buffer (char *buf, idx_t *nread, int *saved_byte)
{
    if (*nread == 0)
        return buf;

    int prev_saved = *saved_byte;
    
    if (should_save_byte(prev_saved, *nread))
        save_last_byte(buf, nread, saved_byte);
    else
        *saved_byte = -1;

    swap_bytes(buf, *nread);
    
    return adjust_buffer_start(buf, prev_saved, nread);
}

/* Add OFFSET to the input offset, setting the overflow flag if
   necessary.  */

static void
advance_input_offset (intmax_t offset)
{
  if (0 <= input_offset && ckd_add (&input_offset, input_offset, offset))
    input_offset = -1;
}

/* Throw away RECORDS blocks of BLOCKSIZE bytes plus BYTES bytes on
   file descriptor FDESC, which is open with read permission for FILE.
   Store up to BLOCKSIZE bytes of the data at a time in IBUF or OBUF, if
   necessary. RECORDS or BYTES must be nonzero. If FDESC is
   STDIN_FILENO, advance the input offset. Return the number of
   records remaining, i.e., that were not skipped because EOF was
   reached.  If FDESC is STDOUT_FILENO, on return, BYTES is the
   remaining bytes in addition to the remaining records.  */

static intmax_t skip_with_lseek(int fdesc, char const *file, off_t offset, intmax_t records, idx_t blocksize, idx_t *bytes)
{
    if (fdesc == STDIN_FILENO)
    {
        struct stat st;
        if (ifstat(STDIN_FILENO, &st) != 0)
            error(EXIT_FAILURE, errno, _("cannot fstat %s"), quoteaf(file));
        if (usable_st_size(&st) && 0 < st.st_size && 0 <= input_offset
            && st.st_size - input_offset < offset)
        {
            records = (offset - st.st_size) / blocksize;
            offset = st.st_size - input_offset;
        }
        else
            records = 0;
        advance_input_offset(offset);
    }
    else
    {
        records = 0;
        *bytes = 0;
    }
    return records;
}

static void handle_seek_end_failure(int fdesc, char const *file, int lseek_errno)
{
    if (!lseek_errno)
        lseek_errno = EOVERFLOW;
    
    diagnose(lseek_errno,
             gettext(fdesc == STDIN_FILENO
                     ? N_("%s: cannot skip")
                     : N_("%s: cannot seek")),
             quotef(file));
    quit(EXIT_FAILURE);
}

static char* allocate_buffer(int fdesc)
{
    if (fdesc == STDIN_FILENO)
    {
        alloc_ibuf();
        return ibuf;
    }
    else
    {
        alloc_obuf();
        return obuf;
    }
}

static void handle_read_error(int fdesc, char const *file, int lseek_errno)
{
    if (fdesc == STDIN_FILENO)
    {
        diagnose(errno, _("error reading %s"), quoteaf(file));
        if (conversions_mask & C_NOERROR)
            print_stats();
    }
    else
        diagnose(lseek_errno, _("%s: cannot seek"), quotef(file));
    quit(EXIT_FAILURE);
}

static intmax_t skip_with_read(int fdesc, char const *file, intmax_t records, idx_t blocksize, idx_t *bytes, int lseek_errno)
{
    char *buf = allocate_buffer(fdesc);
    
    do
    {
        ssize_t nread = iread_fnc(fdesc, buf, records ? blocksize : *bytes);
        if (nread < 0)
        {
            handle_read_error(fdesc, file, lseek_errno);
        }
        else if (nread == 0)
            break;
        else if (fdesc == STDIN_FILENO)
            advance_input_offset(nread);
        
        if (records != 0)
            records--;
        else
            *bytes = 0;
    }
    while (records || *bytes);
    
    return records;
}

static intmax_t skip(int fdesc, char const *file, intmax_t records, idx_t blocksize, idx_t *bytes)
{
    errno = 0;
    off_t offset;
    if (!ckd_mul(&offset, records, blocksize)
        && !ckd_add(&offset, offset, *bytes)
        && 0 <= lseek(fdesc, offset, SEEK_CUR))
    {
        return skip_with_lseek(fdesc, file, offset, records, blocksize, bytes);
    }
    
    int lseek_errno = errno;
    
    if (lseek(fdesc, 0, SEEK_END) >= 0)
    {
        handle_seek_end_failure(fdesc, file, lseek_errno);
    }
    
    return skip_with_read(fdesc, file, records, blocksize, bytes, lseek_errno);
}

/* Advance the input by NBYTES if possible, after a read error.
   The input file offset may or may not have advanced after the failed
   read; adjust it to point just after the bad record regardless.
   Return true if successful, or if the input is already known to not
   be seekable.  */

static bool handle_non_seekable_input(void)
{
    if (input_seek_errno == ESPIPE)
        return true;
    errno = input_seek_errno;
    diagnose(errno, _("%s: cannot seek"), quotef(input_file));
    return false;
}

static bool validate_input_offset(idx_t nbytes)
{
    advance_input_offset(nbytes);
    if (input_offset < 0)
    {
        diagnose(0, _("offset overflow while reading file %s"),
                quoteaf(input_file));
        return false;
    }
    return true;
}

static bool seek_to_input_offset(off_t current_offset)
{
    if (current_offset == input_offset)
        return true;
    
    off_t diff = input_offset - current_offset;
    
    if (!(0 <= diff && diff <= input_offset - current_offset) && status_level != STATUS_NONE)
        diagnose(0, _("warning: invalid file offset after failed read"));
    
    if (0 <= lseek(STDIN_FILENO, diff, SEEK_CUR))
        return true;
    
    if (errno == 0)
        diagnose(0, _("cannot work around kernel bug after all"));
    
    return false;
}

static bool handle_seekable_input(idx_t nbytes)
{
    if (!validate_input_offset(nbytes))
        return false;
    
    off_t offset = lseek(STDIN_FILENO, 0, SEEK_CUR);
    if (offset < 0)
    {
        diagnose(errno, _("%s: cannot seek"), quotef(input_file));
        return false;
    }
    
    if (seek_to_input_offset(offset))
        return true;
    
    diagnose(errno, _("%s: cannot seek"), quotef(input_file));
    return false;
}

static bool advance_input_after_read_error(idx_t nbytes)
{
    if (!input_seekable)
        return handle_non_seekable_input();
    
    return handle_seekable_input(nbytes);
}

/* Copy NREAD bytes of BUF, with no conversions.  */

static void copy_chunk_to_output(char const *source, idx_t size)
{
    memcpy(obuf + oc, source, size);
    oc += size;
}

static void flush_output_if_full(void)
{
    if (oc >= output_blocksize)
        write_output();
}

static idx_t calculate_copy_size(idx_t remaining)
{
    return MIN(remaining, output_blocksize - oc);
}

static void copy_simple(char const *buf, idx_t nread)
{
    char const *start = buf;

    do
    {
        idx_t nfree = calculate_copy_size(nread);
        copy_chunk_to_output(start, nfree);
        
        nread -= nfree;
        start += nfree;
        
        flush_output_if_full();
    }
    while (nread != 0);
}

/* Copy NREAD bytes of BUF, doing conv=block
   (pad newline-terminated records to 'conversion_blocksize',
   replacing the newline with trailing spaces).  */

static void pad_to_block_size(idx_t col)
{
    for (idx_t j = col; j < conversion_blocksize; j++)
        output_char(space_character);
}

static void handle_newline(void)
{
    if (col < conversion_blocksize)
        pad_to_block_size(col);
    col = 0;
}

static void handle_regular_character(char c)
{
    if (col == conversion_blocksize)
        r_truncate++;
    else if (col < conversion_blocksize)
        output_char(c);
    col++;
}

static void copy_with_block(char const *buf, idx_t nread)
{
    for (idx_t i = nread; i; i--, buf++)
    {
        if (*buf == newline_character)
            handle_newline();
        else
            handle_regular_character(*buf);
    }
}

/* Copy NREAD bytes of BUF, doing conv=unblock
   (replace trailing spaces in 'conversion_blocksize'-sized records
   with a newline).  */

static void output_pending_spaces(idx_t *pending_spaces)
{
    while (*pending_spaces > 0)
    {
        output_char(space_character);
        (*pending_spaces)--;
    }
}

static void handle_line_overflow(idx_t *i, idx_t *pending_spaces)
{
    col = 0;
    *pending_spaces = 0;
    (*i)--;
    output_char(newline_character);
}

static void process_space_character(idx_t *pending_spaces)
{
    (*pending_spaces)++;
}

static void process_non_space_character(char c, idx_t *pending_spaces)
{
    output_pending_spaces(pending_spaces);
    output_char(c);
}

static void copy_with_unblock(char const *buf, idx_t nread)
{
    static idx_t pending_spaces = 0;

    for (idx_t i = 0; i < nread; i++)
    {
        char c = buf[i];

        if (col++ >= conversion_blocksize)
        {
            handle_line_overflow(&i, &pending_spaces);
        }
        else if (c == space_character)
        {
            process_space_character(&pending_spaces);
        }
        else
        {
            process_non_space_character(c, &pending_spaces);
        }
    }
}

/* Set the file descriptor flags for FD that correspond to the nonzero bits
   in ADD_FLAGS.  The file's name is NAME.  */

static void
set_fd_flags (int fd, int add_flags, char const *name)
{
  #define FILE_CREATION_FLAGS (O_NOCTTY | O_NOFOLLOW)
  #define VALIDATION_FLAGS (O_DIRECTORY | O_NOLINKS)
  
  add_flags &= ~FILE_CREATION_FLAGS;

  if (!add_flags)
    return;

  int old_flags = fcntl (fd, F_GETFL);
  if (old_flags < 0)
    error (EXIT_FAILURE, errno, _("setting flags for %s"), quoteaf (name));

  int new_flags = old_flags | add_flags;
  if (old_flags == new_flags)
    return;

  if (new_flags & VALIDATION_FLAGS)
    {
      validate_fd_flags (fd, &new_flags, name);
    }

  if (old_flags != new_flags && fcntl (fd, F_SETFL, new_flags) == -1)
    error (EXIT_FAILURE, errno, _("setting flags for %s"), quoteaf (name));
}

static void
validate_fd_flags (int fd, int *new_flags, char const *name)
{
  struct stat st;
  if (ifstat (fd, &st) != 0)
    error (EXIT_FAILURE, errno, _("setting flags for %s"), quoteaf (name));

  if ((*new_flags & O_DIRECTORY) && !S_ISDIR (st.st_mode))
    {
      errno = ENOTDIR;
      error (EXIT_FAILURE, errno, _("setting flags for %s"), quoteaf (name));
    }

  if ((*new_flags & O_NOLINKS) && 1 < st.st_nlink)
    {
      errno = EMLINK;
      error (EXIT_FAILURE, errno, _("setting flags for %s"), quoteaf (name));
    }

  *new_flags &= ~VALIDATION_FLAGS;
}

/* The main loop.  */

static int handle_skip_operation(void)
{
    intmax_t us_bytes;
    bool us_bytes_overflow = 
        (ckd_mul(&us_bytes, skip_records, input_blocksize) ||
         ckd_add(&us_bytes, skip_bytes, us_bytes));
    off_t input_offset0 = input_offset;
    intmax_t us_blocks = skip(STDIN_FILENO, input_file,
                              skip_records, input_blocksize, &skip_bytes);

    if ((us_blocks || (0 <= input_offset && 
        (us_bytes_overflow || us_bytes != input_offset - input_offset0))) &&
        status_level != STATUS_NONE)
    {
        diagnose(0, _("%s: cannot skip to specified offset"), 
                quotef(input_file));
    }
    return 0;
}

static void write_seek_padding(intmax_t write_records, idx_t bytes)
{
    memset(obuf, 0, write_records ? output_blocksize : bytes);
    
    do {
        idx_t size = write_records ? output_blocksize : bytes;
        if (iwrite(STDOUT_FILENO, obuf, size) != size)
        {
            diagnose(errno, _("writing to %s"), quoteaf(output_file));
            quit(EXIT_FAILURE);
        }
        
        if (write_records != 0)
            write_records--;
        else
            bytes = 0;
    } while (write_records || bytes);
}

static int handle_seek_operation(void)
{
    idx_t bytes = seek_bytes;
    intmax_t write_records = skip(STDOUT_FILENO, output_file,
                                  seek_records, output_blocksize, &bytes);

    if (write_records != 0 || bytes != 0)
    {
        write_seek_padding(write_records, bytes);
    }
    return 0;
}

static void prepare_buffer_for_sync_noerror(void)
{
    char fill_char = (conversions_mask & (C_BLOCK | C_UNBLOCK)) ? ' ' : '\0';
    memset(ibuf, fill_char, input_blocksize);
}

static void update_progress(void)
{
    xtime_t progress_time = gethrxtime();
    if (next_time <= progress_time)
    {
        print_xfer_stats(progress_time);
        next_time += XTIME_PRECISION;
    }
}

static ssize_t read_input_block(void)
{
    ssize_t nread;
    
    if (r_partial + r_full >= max_records)
        nread = iread_fnc(STDIN_FILENO, ibuf, max_bytes);
    else
        nread = iread_fnc(STDIN_FILENO, ibuf, input_blocksize);
    
    return nread;
}

static void handle_successful_read(ssize_t nread)
{
    advance_input_offset(nread);
    if (i_nocache)
        invalidate_cache(STDIN_FILENO, nread);
}

static void handle_eof(void)
{
    i_nocache_eof |= i_nocache;
    o_nocache_eof |= o_nocache && !(conversions_mask & C_NOTRUNC);
}

static int handle_read_error(idx_t partread, int *exit_status)
{
    if (!(conversions_mask & C_NOERROR) || status_level != STATUS_NONE)
        diagnose(errno, _("error reading %s"), quoteaf(input_file));

    if (!(conversions_mask & C_NOERROR))
    {
        *exit_status = EXIT_FAILURE;
        return 0;
    }

    print_stats();
    idx_t bad_portion = input_blocksize - partread;
    invalidate_cache(STDIN_FILENO, bad_portion);

    if (!advance_input_after_read_error(bad_portion))
    {
        *exit_status = EXIT_FAILURE;
        input_seekable = false;
        input_seek_errno = ESPIPE;
    }
    
    if ((conversions_mask & C_SYNC) && !partread)
        return 1;
    
    return -1;
}

static void update_read_statistics(idx_t n_bytes_read, idx_t *partread)
{
    if (n_bytes_read < input_blocksize)
    {
        r_partial++;
        *partread = n_bytes_read;
    }
    else
    {
        r_full++;
        *partread = 0;
    }
}

static idx_t sync_partial_block(idx_t n_bytes_read)
{
    if (!(conversions_mask & C_NOERROR))
    {
        char fill_char = (conversions_mask & (C_BLOCK | C_UNBLOCK)) ? ' ' : '\0';
        memset(ibuf + n_bytes_read, fill_char, input_blocksize - n_bytes_read);
    }
    return input_blocksize;
}

static int write_direct_output(idx_t n_bytes_read)
{
    idx_t nwritten = iwrite(STDOUT_FILENO, obuf, n_bytes_read);
    w_bytes += nwritten;
    
    if (nwritten != n_bytes_read)
    {
        diagnose(errno, _("error writing %s"), quoteaf(output_file));
        return EXIT_FAILURE;
    }
    
    if (n_bytes_read == input_blocksize)
        w_full++;
    else
        w_partial++;
    
    return 0;
}

static void process_buffer_conversions(char **bufstart, idx_t *n_bytes_read, int *saved_byte)
{
    if (translation_needed)
        translate_buffer(ibuf, *n_bytes_read);

    if (conversions_mask & C_SWAB)
        *bufstart = swab_buffer(ibuf, n_bytes_read, saved_byte);
    else
        *bufstart = ibuf;
}

static void copy_buffer_with_conversion(char *bufstart, idx_t n_bytes_read)
{
    if (conversions_mask & C_BLOCK)
        copy_with_block(bufstart, n_bytes_read);
    else if (conversions_mask & C_UNBLOCK)
        copy_with_unblock(bufstart, n_bytes_read);
    else
        copy_simple(bufstart, n_bytes_read);
}

static void output_saved_byte(int saved_byte)
{
    char saved_char = saved_byte;
    
    if (conversions_mask & C_BLOCK)
        copy_with_block(&saved_char, 1);
    else if (conversions_mask & C_UNBLOCK)
        copy_with_unblock(&saved_char, 1);
    else
        output_char(saved_char);
}

static void pad_final_block(void)
{
    for (idx_t i = col; i < conversion_blocksize; i++)
        output_char(space_character);
}

static int write_final_block(void)
{
    idx_t nwritten = iwrite(STDOUT_FILENO, obuf, oc);
    w_bytes += nwritten;
    
    if (nwritten != 0)
        w_partial++;
    
    if (nwritten != oc)
    {
        diagnose(errno, _("error writing %s"), quoteaf(output_file));
        return EXIT_FAILURE;
    }
    
    return 0;
}

static int handle_final_seek(void)
{
    struct stat stdout_stat;
    
    if (ifstat(STDOUT_FILENO, &stdout_stat) != 0)
    {
        diagnose(errno, _("cannot fstat %s"), quoteaf(output_file));
        return EXIT_FAILURE;
    }
    
    if (!S_ISREG(stdout_stat.st_mode) && !S_TYPEISSHM(&stdout_stat))
        return 0;
    
    off_t output_offset = lseek(STDOUT_FILENO, 0, SEEK_CUR);
    
    if (0 <= output_offset && stdout_stat.st_size < output_offset)
    {
        if (iftruncate(STDOUT_FILENO, output_offset) != 0)
        {
            diagnose(errno, _("failed to truncate to %jd bytes"
                            " in output file %s"),
                    (intmax_t) output_offset, quoteaf(output_file));
            return EXIT_FAILURE;
        }
    }
    
    return 0;
}

static void show_final_progress(void)
{
    if ((conversions_mask & (C_FDATASYNC | C_FSYNC)) &&
        status_level == STATUS_PROGRESS &&
        0 <= reported_w_bytes && reported_w_bytes < w_bytes)
    {
        print_xfer_stats(0);
    }
}

static int dd_copy(void)
{
    char *bufstart;
    ssize_t nread;
    idx_t partread = 0;
    int exit_status = EXIT_SUCCESS;
    idx_t n_bytes_read;

    if (skip_records != 0 || skip_bytes != 0)
        handle_skip_operation();

    if (seek_records != 0 || seek_bytes != 0)
        handle_seek_operation();

    if (max_records == 0 && max_bytes == 0)
        return exit_status;

    alloc_ibuf();
    alloc_obuf();
    int saved_byte = -1;

    while (true)
    {
        if (status_level == STATUS_PROGRESS)
            update_progress();

        if (r_partial + r_full >= max_records + !!max_bytes)
            break;

        if ((conversions_mask & C_SYNC) && (conversions_mask & C_NOERROR))
            prepare_buffer_for_sync_noerror();

        nread = read_input_block();

        if (nread > 0)
        {
            handle_successful_read(nread);
        }
        else if (nread == 0)
        {
            handle_eof();
            break;
        }
        else
        {
            int result = handle_read_error(partread, &exit_status);
            if (result == 0)
                break;
            else if (result == 1)
                nread = 0;
            else
                continue;
        }

        n_bytes_read = nread;
        update_read_statistics(n_bytes_read, &partread);

        if (n_bytes_read < input_blocksize && (conversions_mask & C_SYNC))
            n_bytes_read = sync_partial_block(n_bytes_read);

        if (ibuf == obuf)
        {
            int result = write_direct_output(n_bytes_read);
            if (result != 0)
                return result;
            continue;
        }

        process_buffer_conversions(&bufstart, &n_bytes_read, &saved_byte);
        copy_buffer_with_conversion(bufstart, n_bytes_read);
    }

    if (0 <= saved_byte)
        output_saved_byte(saved_byte);

    if ((conversions_mask & C_BLOCK) && col > 0)
        pad_final_block();

    if (col && (conversions_mask & C_UNBLOCK))
        output_char(newline_character);

    if (oc != 0)
    {
        int result = write_final_block();
        if (result != 0)
            return result;
    }

    if (final_op_was_seek)
    {
        int result = handle_final_seek();
        if (result != 0)
            return result;
    }

    show_final_progress();
    
    return exit_status;
}

/* Synchronize output according to conversions_mask.
   Do this even if w_bytes is zero, as fsync and fdatasync
   flush out write requests from other processes too.
   Clear bits in conversions_mask so that synchronization is done only once.
   Return zero if successful, an exit status otherwise.  */

static int try_fdatasync(int *mask)
{
    if (!(*mask & C_FDATASYNC))
        return 0;
    
    if (ifdatasync(STDOUT_FILENO) == 0)
        return 0;
    
    if (errno != ENOSYS && errno != EINVAL)
    {
        diagnose(errno, _("fdatasync failed for %s"), quoteaf(output_file));
        return EXIT_FAILURE;
    }
    
    *mask |= C_FSYNC;
    return 0;
}

static int try_fsync(int mask)
{
    if (!(mask & C_FSYNC))
        return 0;
    
    if (ifsync(STDOUT_FILENO) == 0)
        return 0;
    
    diagnose(errno, _("fsync failed for %s"), quoteaf(output_file));
    return EXIT_FAILURE;
}

static int synchronize_output(void)
{
    int mask = conversions_mask;
    conversions_mask &= ~(C_FDATASYNC | C_FSYNC);
    
    int exit_status = try_fdatasync(&mask);
    if (exit_status != 0)
        return exit_status;
    
    return try_fsync(mask);
}

int
main (int argc, char **argv)
{
  int exit_status;

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

  initialize_translation_table ();
  scanargs (argc, argv);
  apply_translations ();

  open_input_file ();
  check_input_seekability ();
  open_output_file ();

  start_time = gethrxtime ();
  next_time = start_time + XTIME_PRECISION;

  exit_status = dd_copy ();

  int sync_status = synchronize_output ();
  if (sync_status)
    exit_status = sync_status;

  exit_status = handle_cache_invalidation (exit_status);

  finish_up ();
  main_exit (exit_status);
}

static void
initialize_translation_table (void)
{
  for (int i = 0; i < 256; i++)
    trans_table[i] = i;
}

static void
open_input_file (void)
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
}

static void
check_input_seekability (void)
{
  off_t offset = lseek (STDIN_FILENO, 0, SEEK_CUR);
  input_seekable = (0 <= offset);
  input_offset = MAX (0, offset);
  input_seek_errno = errno;
}

static void
open_output_file (void)
{
  if (output_file == nullptr)
    {
      output_file = _("standard output");
      set_fd_flags (STDOUT_FILENO, output_flags, output_file);
    }
  else
    {
      open_output_file_with_options ();
    }
}

static void
open_output_file_with_options (void)
{
  mode_t perms = MODE_RW_UGO;
  int opts = calculate_output_options ();
  off_t size = calculate_output_size ();

  if (!try_open_output_file (opts, perms))
    error (EXIT_FAILURE, errno, _("failed to open %s"),
           quoteaf (output_file));

  if (seek_records != 0 && !(conversions_mask & C_NOTRUNC))
    handle_output_truncation (size);
}

static int
calculate_output_options (void)
{
  return (output_flags
          | (conversions_mask & C_NOCREAT ? 0 : O_CREAT)
          | (conversions_mask & C_EXCL ? O_EXCL : 0)
          | (seek_records || (conversions_mask & C_NOTRUNC) ? 0 : O_TRUNC));
}

static off_t
calculate_output_size (void)
{
  off_t size;
  if ((ckd_mul (&size, seek_records, output_blocksize)
       || ckd_add (&size, seek_bytes, size))
      && !(conversions_mask & C_NOTRUNC))
    error (EXIT_FAILURE, 0,
           _("offset too large: "
             "cannot truncate to a length of seek=%jd"
             " (%td-byte) blocks"),
           seek_records, output_blocksize);
  return size;
}

static bool
try_open_output_file (int opts, mode_t perms)
{
  if (seek_records)
    {
      if (ifd_reopen (STDOUT_FILENO, output_file, O_RDWR | opts, perms) >= 0)
        return true;
    }
  return ifd_reopen (STDOUT_FILENO, output_file, O_WRONLY | opts, perms) >= 0;
}

static void
handle_output_truncation (off_t size)
{
  if (iftruncate (STDOUT_FILENO, size) != 0)
    {
      int ftruncate_errno = errno;
      struct stat stdout_stat;
      if (ifstat (STDOUT_FILENO, &stdout_stat) != 0)
        {
          diagnose (errno, _("cannot fstat %s"), quoteaf (output_file));
          exit_status = EXIT_FAILURE;
        }
      else if (should_report_truncation_error (&stdout_stat))
        {
          intmax_t isize = size;
          diagnose (ftruncate_errno,
                    _("failed to truncate to %jd bytes"
                      " in output file %s"),
                    isize, quoteaf (output_file));
          exit_status = EXIT_FAILURE;
        }
    }
}

static bool
should_report_truncation_error (struct stat *st)
{
  return S_ISREG (st->st_mode) || S_ISDIR (st->st_mode) || S_TYPEISSHM (st);
}

static int
handle_cache_invalidation (int exit_status)
{
  if (max_records == 0 && max_bytes == 0)
    return invalidate_special_case (exit_status);
  else
    return invalidate_normal_case (exit_status);
}

static int
invalidate_special_case (int exit_status)
{
  if (i_nocache && !invalidate_cache (STDIN_FILENO, 0))
    {
      diagnose (errno, _("failed to discard cache for: %s"),
                quotef (input_file));
      exit_status = EXIT_FAILURE;
    }
  if (o_nocache && !invalidate_cache (STDOUT_FILENO, 0))
    {
      diagnose (errno, _("failed to discard cache for: %s"),
                quotef (output_file));
      exit_status = EXIT_FAILURE;
    }
  return exit_status;
}

static int
invalidate_normal_case (int exit_status)
{
  if (i_nocache || i_nocache_eof)
    invalidate_cache (STDIN_FILENO, 0);
  if (o_nocache || o_nocache_eof)
    invalidate_cache (STDOUT_FILENO, 0);
  return exit_status;
}
