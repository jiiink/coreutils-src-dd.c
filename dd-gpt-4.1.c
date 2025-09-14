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
static void maybe_close_stdout(void)
{
    if (close_stdout_required) {
        close_stdout();
        return;
    }
    if (close_stream(stderr) != 0) {
        _exit(EXIT_FAILURE);
    }
}

/* Like the 'error' function but handle any pending newline,
   and do not exit.  */

ATTRIBUTE_FORMAT ((__printf__, 2, 3))
static void diagnose(int errnum, const char *fmt, ...)
{
    va_list ap;

    if (progress_len > 0)
    {
        if (fputc('\n', stderr) == EOF)
        {
            /* Optionally handle the error */
        }
        progress_len = 0;
    }

    va_start(ap, fmt);
    verror(0, errnum, fmt, ap);
    va_end(ap);
}

void usage(int status) {
    if (status != EXIT_SUCCESS) {
        emit_try_help();
    } else {
        printf(_(
            "Usage: %s [OPERAND]...\n"
            "  or:  %s OPTION\n"
        ), program_name, program_name);

        fputs(_(
            "Copy a file, converting and formatting according to the operands.\n"
            "\n"
            "  bs=BYTES        read and write up to BYTES bytes at a time (default: 512);\n"
            "                  overrides ibs and obs\n"
            "  cbs=BYTES       convert BYTES bytes at a time\n"
            "  conv=CONVS      convert the file as per the comma separated symbol list\n"
            "  count=N         copy only N input blocks\n"
            "  ibs=BYTES       read up to BYTES bytes at a time (default: 512)\n"
        ), stdout);

        fputs(_(
            "  if=FILE         read from FILE instead of standard input\n"
            "  iflag=FLAGS     read as per the comma separated symbol list\n"
            "  obs=BYTES       write BYTES bytes at a time (default: 512)\n"
            "  of=FILE         write to FILE instead of standard output\n"
            "  oflag=FLAGS     write as per the comma separated symbol list\n"
            "  seek=N          (or oseek=N) skip N obs-sized output blocks\n"
            "  skip=N          (or iseek=N) skip N ibs-sized input blocks\n"
            "  status=LEVEL    The LEVEL of information to print to standard error;\n"
            "                  'none' suppresses everything but error messages,\n"
            "                  'noxfer' suppresses the final transfer statistics,\n"
            "                  'progress' shows periodic transfer statistics\n"
        ), stdout);

        fputs(_(
            "\n"
            "N and BYTES may be followed by the following multiplicative suffixes:\n"
            "c=1, w=2, b=512, kB=1000, K=1024, MB=1000*1000, M=1024*1024, xM=M,\n"
            "GB=1000*1000*1000, G=1024*1024*1024, and so on for T, P, E, Z, Y, R, Q.\n"
            "Binary prefixes can be used, too: KiB=K, MiB=M, and so on.\n"
            "If N ends in 'B', it counts bytes not blocks.\n"
            "\n"
            "Each CONV symbol may be:\n"
            "\n"
        ), stdout);

        fputs(_(
            "  ascii     from EBCDIC to ASCII\n"
            "  ebcdic    from ASCII to EBCDIC\n"
            "  ibm       from ASCII to alternate EBCDIC\n"
            "  block     pad newline-terminated records with spaces to cbs-size\n"
            "  unblock   replace trailing spaces in cbs-size records with newline\n"
            "  lcase     change upper case to lower case\n"
            "  ucase     change lower case to upper case\n"
            "  sparse    try to seek rather than write all-NUL output blocks\n"
            "  swab      swap every pair of input bytes\n"
            "  sync      pad every input block with NULs to ibs-size; when used\n"
            "            with block or unblock, pad with spaces rather than NULs\n"
        ), stdout);

        fputs(_(
            "  excl      fail if the output file already exists\n"
            "  nocreat   do not create the output file\n"
            "  notrunc   do not truncate the output file\n"
            "  noerror   continue after read errors\n"
            "  fdatasync  physically write output file data before finishing\n"
            "  fsync     likewise, but also write metadata\n"
        ), stdout);

        fputs(_(
            "\n"
            "Each FLAG symbol may be:\n"
            "\n"
            "  append    append mode (makes sense only for output; conv=notrunc suggested)\n"
        ), stdout);

        if (O_CIO)       fputs(_("  cio       use concurrent I/O for data\n"), stdout);
        if (O_DIRECT)    fputs(_("  direct    use direct I/O for data\n"), stdout);
        fputs(_("  directory  fail unless a directory\n"), stdout);
        if (O_DSYNC)     fputs(_("  dsync     use synchronized I/O for data\n"), stdout);
        if (O_SYNC)      fputs(_("  sync      likewise, but also for metadata\n"), stdout);
        fputs(_("  fullblock  accumulate full blocks of input (iflag only)\n"), stdout);
        if (O_NONBLOCK)  fputs(_("  nonblock  use non-blocking I/O\n"), stdout);
        if (O_NOATIME)   fputs(_("  noatime   do not update access time\n"), stdout);
#if HAVE_POSIX_FADVISE
        if (O_NOCACHE)   fputs(_("  nocache   Request to drop cache.  See also oflag=sync\n"), stdout);
#endif
        if (O_NOCTTY)    fputs(_("  noctty    do not assign controlling terminal from file\n"), stdout);
        if (HAVE_WORKING_O_NOFOLLOW) fputs(_("  nofollow  do not follow symlinks\n"), stdout);
        if (O_NOLINKS)   fputs(_("  nolinks   fail if multiply-linked\n"), stdout);
        if (O_BINARY)    fputs(_("  binary    use binary I/O for data\n"), stdout);
        if (O_TEXT)      fputs(_("  text      use text I/O for data\n"), stdout);

        printf(_(
            "\n"
            "Sending a %s signal to a running 'dd' process makes it\n"
            "print I/O statistics to standard error and then resume copying.\n"
            "\n"
            "Options are:\n"
            "\n"
        ), SIGINFO == SIGUSR1 ? "USR1" : "INFO");

        fputs(HELP_OPTION_DESCRIPTION, stdout);
        fputs(VERSION_OPTION_DESCRIPTION, stdout);
        emit_ancillary_info(PROGRAM_NAME);
    }
    exit(status);
}

/* Common options to use when displaying sizes and rates.  */

enum { human_opts = (human_autoscale | human_round_to_nearest
                     | human_space_before_unit | human_SI | human_B) };

/* Ensure input buffer IBUF is allocated.  */

static void alloc_ibuf(void)
{
    if (ibuf)
        return;

    bool extra_byte_for_swab = (conversions_mask & C_SWAB) != 0;
    size_t total_size = input_blocksize + (extra_byte_for_swab ? 1 : 0);

    ibuf = alignalloc(page_size, total_size);
    if (!ibuf)
    {
        char hbuf[LONGEST_HUMAN_READABLE + 1];
        const char *hr = human_readable(input_blocksize, hbuf, human_opts | human_base_1024, 1, 1);
        error(EXIT_FAILURE, 0,
              _("memory exhausted by input buffer of size %td bytes (%s)"),
              input_blocksize, hr);
    }
}

/* Ensure output buffer OBUF is allocated/initialized.  */

static void alloc_obuf(void) {
    if (obuf) {
        return;
    }

    if ((conversions_mask & C_TWOBUFS) != 0) {
        obuf = alignalloc(page_size, output_blocksize);
        if (!obuf) {
            char hbuf[LONGEST_HUMAN_READABLE + 1];
            const char *hr = human_readable(output_blocksize, hbuf, human_opts | human_base_1024, 1, 1);
            error(EXIT_FAILURE, 0,
                  _("memory exhausted by output buffer of size %td bytes (%s)"),
                  output_blocksize, hr);
        }
    } else {
        alloc_ibuf();
        obuf = ibuf;
    }
}

static void translate_charset(const char *new_trans)
{
    if (!new_trans)
        return;

    for (int i = 0; i < 256; ++i) {
        unsigned char idx = trans_table[i];
        trans_table[i] = new_trans[idx];
    }
    translation_needed = true;
}


/* Return true if I has more than one bit set.  I must be nonnegative.  */

static inline bool multiple_bits_set(int i)
{
    return (i & (i - 1)) != 0 && i != 0;
}

static bool abbreviation_lacks_prefix(const char *message) {
    size_t len;
    if (!message)
        return false;
    len = strlen(message);
    if (len < 2)
        return false;
    return message[len - 2] == ' ';
}

/* Print transfer statistics.  */

static void print_xfer_stats(xtime_t progress_time)
{
    xtime_t now = progress_time ? progress_time : gethrxtime();
    static const char slash_s[] = "/s";
    char hbuf[3][LONGEST_HUMAN_READABLE + sizeof(slash_s)];
    double delta_s = 0.0;
    char *bpsbuf = hbuf[2];
    size_t bpsbufsize = sizeof(hbuf[2]);
    char const *bytes_per_second;
    char const *si, *iec;

    si = human_readable(w_bytes, hbuf[0], human_opts, 1, 1);
    iec = human_readable(w_bytes, hbuf[1], human_opts | human_base_1024, 1, 1);

    if (start_time < now) {
        xtime_t delta_xtime = now - start_time;
        double xtime_prec = (double)XTIME_PRECISION;
        delta_s = delta_xtime / xtime_prec;

        bytes_per_second = human_readable(w_bytes, bpsbuf, human_opts, XTIME_PRECISION, delta_xtime);
        size_t offset = strlen(bpsbuf);
        if (offset + strlen(slash_s) < bpsbufsize)
            strcat(bpsbuf, slash_s);
        else
            strncat(bpsbuf, slash_s, bpsbufsize - offset - 1);
    } else {
        snprintf(bpsbuf, bpsbufsize, "%s B/s", _("Infinity"));
        bytes_per_second = bpsbuf;
        delta_s = 0.0;
    }

    if (progress_time)
        fputc('\r', stderr);

    char delta_s_buf[24];
    if (progress_time)
        snprintf(delta_s_buf, sizeof(delta_s_buf), "%.0f s", delta_s);
    else
        snprintf(delta_s_buf, sizeof(delta_s_buf), "%g s", delta_s);

    int stats_len = 0;
    if (abbreviation_lacks_prefix(si)) {
        stats_len = fprintf(stderr,
                            ngettext("%jd byte copied, %s, %s",
                                     "%jd bytes copied, %s, %s",
                                     select_plural(w_bytes)),
                            w_bytes, delta_s_buf, bytes_per_second);
    } else if (abbreviation_lacks_prefix(iec)) {
        stats_len = fprintf(stderr,
                            _("%jd bytes (%s) copied, %s, %s"),
                            w_bytes, si, delta_s_buf, bytes_per_second);
    } else {
        stats_len = fprintf(stderr,
                            _("%jd bytes (%s, %s) copied, %s, %s"),
                            w_bytes, si, iec, delta_s_buf, bytes_per_second);
    }

    if (progress_time) {
        if (stats_len >= 0 && stats_len < progress_len)
            fprintf(stderr, "%*s", progress_len - stats_len, "");
        progress_len = (stats_len >= 0) ? stats_len : 0;
    } else {
        fputc('\n', stderr);
    }

    reported_w_bytes = w_bytes;
}

static void print_stats(void)
{
    if (status_level == STATUS_NONE)
        return;

    if (progress_len > 0) {
        fputc('\n', stderr);
        progress_len = 0;
    }

    fprintf(stderr,
            _("%jd+%jd records in\n"
              "%jd+%jd records out\n"),
            r_full, r_partial, w_full, w_partial);

    if (r_truncate != 0) {
        fprintf(stderr,
                ngettext("%jd truncated record\n",
                         "%jd truncated records\n",
                         r_truncate),
                r_truncate);
    }

    if (status_level != STATUS_NOXFER) {
        print_xfer_stats(0);
    }
}

/* An ordinary signal was received; arrange for the program to exit.  */

static void interrupt_handler(int sig)
{
    if (SA_RESETHAND == 0) {
        if (signal(sig, SIG_DFL) == SIG_ERR) {
            /* handle error if needed */
        }
    }
    interrupt_signal = sig;
}

/* An info signal was received; arrange for the program to print status.  */

static void siginfo_handler(int sig)
{
    if (!SA_NOCLDSTOP) {
        if (signal(sig, siginfo_handler) == SIG_ERR) {
            return;
        }
    }
    info_signal_count++;
}

/* Install the signal handlers.  */

static void install_signal_handlers(void) {
    bool catch_siginfo = !(SIGINFO == SIGUSR1 && getenv("POSIXLY_CORRECT"));

#if SA_NOCLDSTOP
    struct sigaction act;
    sigset_t signals_to_catch;
    sigemptyset(&signals_to_catch);
    if (catch_siginfo)
        sigaddset(&signals_to_catch, SIGINFO);

    if (sigaction(SIGINT, NULL, &act) == 0 && act.sa_handler != SIG_IGN)
        sigaddset(&signals_to_catch, SIGINT);

    act.sa_mask = signals_to_catch;

    if (sigismember(&signals_to_catch, SIGINFO)) {
        act.sa_handler = siginfo_handler;
        act.sa_flags = 0;
        sigaction(SIGINFO, &act, NULL);
    }

    if (sigismember(&signals_to_catch, SIGINT)) {
        act.sa_handler = interrupt_handler;
        act.sa_flags = SA_NODEFER | SA_RESETHAND;
        sigaction(SIGINT, &act, NULL);
    }

#else
    if (catch_siginfo) {
        signal(SIGINFO, siginfo_handler);
        siginterrupt(SIGINFO, 1);
    }
    if (signal(SIGINT, SIG_IGN) != SIG_IGN) {
        signal(SIGINT, interrupt_handler);
        siginterrupt(SIGINT, 1);
    }
#endif
}

/* Close FD.  Return 0 if successful, -1 (setting errno) otherwise.
   If close fails with errno == EINTR, POSIX says the file descriptor
   is in an unspecified state, so keep trying to close FD but do not
   consider EBADF to be an error.  Do not process signals.  This all
   differs somewhat from functions like ifdatasync and ifsync.  */
static int iclose(int fd) {
    int ret;
    do {
        ret = close(fd);
        if (ret == 0)
            return 0;
        if (errno == EBADF)
            return -1;
        if (errno != EINTR)
            return -1;
    } while (1);
}

static int synchronize_output (void);

static void cleanup(void)
{
    int result;

    if (!interrupt_signal)
    {
        int sync_status = synchronize_output();
        if (sync_status != 0)
        {
            exit(sync_status);
        }
    }

    result = iclose(STDIN_FILENO);
    if (result != 0)
    {
        error(EXIT_FAILURE, errno, _("closing input file %s"), quoteaf(input_file));
    }

    result = iclose(STDOUT_FILENO);
    if (result != 0)
    {
        error(EXIT_FAILURE, errno, _("closing output file %s"), quoteaf(output_file));
    }
}

/* Process any pending signals.  If signals are caught, this function
   should be called periodically.  Ideally there should never be an
   unbounded amount of time when signals are not being processed.  */

static void process_signals(void) {
    while (interrupt_signal || info_signal_count) {
        int interrupt = 0;
        int infos = 0;
        sigset_t oldset;

        if (sigprocmask(SIG_BLOCK, &caught_signals, &oldset) == -1)
            return;

        interrupt = interrupt_signal;
        infos = info_signal_count;

        if (infos > 0)
            info_signal_count--;

        if (sigprocmask(SIG_SETMASK, &oldset, NULL) == -1)
            return;

        if (interrupt) {
            cleanup();
        }

        print_stats();

        if (interrupt) {
            raise(interrupt);
        }
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

    /* In case exit() fails to terminate the process, use _exit() as a fallback */
    exit(code);
    _exit(code);
}

/* Return LEN rounded down to a multiple of IO_BUFSIZE
   (to minimize calls to the expensive posix_fadvise (,POSIX_FADV_DONTNEED),
   while storing the remainder internally per FD.
   Pass LEN == 0 to get the current remainder.  */

#include <unistd.h>
#include <stdint.h>
#include <limits.h>

#define IO_BUFSIZE 4096

static off_t cache_round(int fd, off_t len) {
    static off_t i_pending = 0, o_pending = 0;
    off_t *pending = (fd == STDIN_FILENO) ? &i_pending : &o_pending;

    if (len > 0) {
        intmax_t c_pending;
        if (__builtin_add_overflow(*pending, len, &c_pending)) {
            c_pending = INTMAX_MAX;
        }
        *pending = (off_t)(c_pending % IO_BUFSIZE);
        if (c_pending >= (intmax_t)(*pending)) {
            len = (off_t)(c_pending - *pending);
        } else {
            len = 0;
        }
    } else {
        len = *pending;
    }

    return len;
}

/* Discard the cache from the current offset of either
   STDIN_FILENO or STDOUT_FILENO.
   Return true on success.
   Return false on failure, with errno set.  */

static bool invalidate_cache(int fd, off_t len) {
    int adv_ret = -1;
    off_t offset = -1;
    bool nocache_eof = (fd == STDIN_FILENO) ? i_nocache_eof : o_nocache_eof;
    off_t clen = cache_round(fd, len);
    off_t pending = (len) ? cache_round(fd, 0) : 0;

    if ((len && !clen) || (!len && !clen && !nocache_eof)) {
        return true;
    }

    if (fd == STDIN_FILENO) {
        if (input_seekable) {
            offset = input_offset;
        } else {
            errno = ESPIPE;
            return false;
        }
    } else {
        static off_t output_offset = -2;
        if (output_offset != -1) {
            if (output_offset < 0) {
                off_t tmp = lseek(fd, 0, SEEK_CUR);
                if (tmp < 0) {
                    errno = ESPIPE;
                    return false;
                }
                output_offset = tmp;
            } else if (len) {
                output_offset += clen + pending;
            }
        }
        offset = output_offset;
    }

    if (offset < 0) {
        errno = ESPIPE;
        return false;
    }

    if (!len && clen && nocache_eof) {
        pending = clen;
        clen = 0;
    }

#if HAVE_POSIX_FADVISE
    off_t advise_offset = offset - clen - pending;
    if (clen == 0 && page_size > 0) {
        advise_offset -= advise_offset % page_size;
    }
    adv_ret = posix_fadvise(fd, advise_offset, clen, POSIX_FADV_DONTNEED);
    errno = (adv_ret == 0) ? 0 : adv_ret;
#else
    errno = ENOTSUP;
    adv_ret = -1;
#endif

    return adv_ret == 0;
}

/* Read from FD into the buffer BUF of size SIZE, processing any
   signals that arrive before bytes are read.  Return the number of
   bytes read if successful, -1 (setting errno) on failure.  */

static ssize_t iread(int fd, char *buf, idx_t size) {
    ssize_t nread = 0;
    static ssize_t prev_nread = 0;
    bool partial_read_warned = false;

    do {
        process_signals();
        nread = read(fd, buf, size);

        if (nread == -1 && errno == EINVAL &&
            prev_nread > 0 && prev_nread < size &&
            (input_flags & O_DIRECT))
        {
            errno = 0;
            nread = 0;
        }
    } while (nread < 0 && errno == EINTR);

    if (nread > 0 && nread < size)
        process_signals();

    if (nread > 0 && warn_partial_read && prev_nread > 0 && prev_nread < size) {
        if (status_level != STATUS_NONE) {
            idx_t prev = prev_nread;
            diagnose(0, ngettext(
                "warning: partial read (%td byte); suggest iflag=fullblock",
                "warning: partial read (%td bytes); suggest iflag=fullblock",
                select_plural(prev)),
                prev);
        }
        warn_partial_read = false;
    }

    prev_nread = nread;
    return nread;
}

/* Wrapper around iread function to accumulate full blocks.  */
static ssize_t iread_fullblock(int fd, char *buf, idx_t size) {
    ssize_t total_read = 0;

    while (size > 0) {
        ssize_t ncurr = iread(fd, buf, size);
        if (ncurr < 0) {
            return -1;
        }
        if (ncurr == 0) {
            break;
        }
        total_read += ncurr;
        buf += ncurr;
        size -= ncurr;
    }

    return total_read > 0 ? total_read : 0;
}

/* Write to FD the buffer BUF of size SIZE, processing any signals
   that arrive.  Return the number of bytes written, setting errno if
   this is less than SIZE.  Keep trying if there are partial
   writes.  */

static idx_t
iwrite(int fd, char const *buf, idx_t size)
{
    idx_t total_written = 0;

    if ((output_flags & O_DIRECT) && size < output_blocksize) {
        int old_flags = fcntl(STDOUT_FILENO, F_GETFL);
        if (old_flags == -1) {
            if (status_level != STATUS_NONE)
                diagnose(errno, _("failed to get file flags: %s"), quotef(output_file));
        } else if (fcntl(STDOUT_FILENO, F_SETFL, old_flags & ~O_DIRECT) != 0) {
            if (status_level != STATUS_NONE)
                diagnose(errno, _("failed to turn off O_DIRECT: %s"), quotef(output_file));
        }

        o_nocache_eof = true;
        invalidate_cache(STDOUT_FILENO, 0);
        conversions_mask |= C_FSYNC;
    }

    while (total_written < size) {
        ssize_t nwritten;

        process_signals();

        final_op_was_seek = false;
        if ((conversions_mask & C_SPARSE) && is_nul(buf, size)) {
            if (lseek(fd, size, SEEK_CUR) < 0) {
                conversions_mask &= ~C_SPARSE;
            } else {
                final_op_was_seek = true;
                nwritten = size;
                total_written += nwritten;
                continue;
            }
        }

        nwritten = write(fd, buf + total_written, size - total_written);

        if (nwritten < 0) {
            if (errno != EINTR)
                break;
        } else if (nwritten == 0) {
            errno = ENOSPC;
            break;
        } else {
            total_written += nwritten;
        }
    }

    if (o_nocache && total_written)
        invalidate_cache(fd, total_written);

    return total_written;
}

/* Write, then empty, the output buffer 'obuf'. */

static void write_output(void)
{
    idx_t nwritten = iwrite(STDOUT_FILENO, obuf, output_blocksize);

    w_bytes += nwritten;

    if (nwritten == output_blocksize) {
        w_full++;
        oc = 0;
        return;
    }

    diagnose(errno, _("writing to %s"), quoteaf(output_file));
    if (nwritten != 0)
        w_partial++;
    quit(EXIT_FAILURE);
}

/* Restart on EINTR from fdatasync.  */

static int ifdatasync(int fd)
{
    int ret;
    do {
        process_signals();
        ret = fdatasync(fd);
        if (ret == 0)
            break;
        if (ret < 0 && errno != EINTR)
            break;
    } while (ret < 0 && errno == EINTR);
    return ret;
}

/* Restart on EINTR from fd_reopen.  */

static int
ifd_reopen(int desired_fd, const char *file, int flag, mode_t mode)
{
    int ret;
    if (!file)
        return -1;
    do {
        process_signals();
        ret = fd_reopen(desired_fd, file, flag, mode);
    } while (ret < 0 && errno == EINTR);
    return ret;
}

/* Restart on EINTR from fstat.  */

static int ifstat(int fd, struct stat *st) {
    int ret;
    if (!st) {
        errno = EINVAL;
        return -1;
    }
    do {
        process_signals();
        ret = fstat(fd, st);
    } while (ret == -1 && errno == EINTR);
    return ret;
}

/* Restart on EINTR from fsync.  */

static int ifsync(int fd)
{
    int ret;
    do {
        process_signals();
        ret = fsync(fd);
        if (ret < 0 && errno != EINTR) {
            break;
        }
    } while (ret < 0 && errno == EINTR);
    return ret;
}

/* Restart on EINTR from ftruncate.  */

static int iftruncate(int fd, off_t length) {
    int ret;
    do {
        process_signals();
        ret = ftruncate(fd, length);
        if (ret == 0) {
            return 0;
        }
        if (errno != EINTR) {
            break;
        }
    } while (1);
    return -1;
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

static int parse_symbols(const char *str, const struct symbol_value *table, bool exclusive, const char *error_msgid) {
    int value = 0;

    while (str && *str) {
        const char *strcomma = strchr(str, ',');
        size_t slen = strcomma ? (size_t)(strcomma - str) : strlen(str);
        const struct symbol_value *entry = table;
        bool found = false;

        while (entry->symbol[0]) {
            if (operand_matches(str, entry->symbol, ',')) {
                found = entry->value != 0;
                break;
            }
            entry++;
        }

        if (!found) {
            diagnose(0, "%s: %s", _(error_msgid),
                     quotearg_n_style_mem(0, locale_quoting_style, str, slen));
            usage(EXIT_FAILURE);
        }

        if (exclusive)
            value = entry->value;
        else
            value |= entry->value;

        if (!strcomma)
            break;
        str = strcomma + 1;
    }

    return value;
}

/* Return the value of STR, interpreted as a non-negative decimal integer,
   optionally multiplied by various values.
   Set *INVALID to an appropriate error value and return INTMAX_MAX if
   it is an overflow, an indeterminate value if some other error occurred.  */

static intmax_t parse_integer(const char *str, strtol_error *invalid) {
    intmax_t result = 0;
    uintmax_t n = 0;
    char *suffix = NULL;
    static const char suffixes[] = "bcEGkKMPQRTwYZ0";
    strtol_error e = xstrtoumax(str, &suffix, 10, &n, suffixes);

    if ((e & ~LONGINT_OVERFLOW) == LONGINT_INVALID_SUFFIX_CHAR
        && *suffix == 'B' && str < suffix && suffix[-1] != 'B') {
        suffix++;
        if (!*suffix)
            e &= ~LONGINT_INVALID_SUFFIX_CHAR;
    }

    if ((e & ~LONGINT_OVERFLOW) == LONGINT_INVALID_SUFFIX_CHAR && *suffix == 'x') {
        strtol_error f = LONGINT_OK;
        intmax_t o = parse_integer(suffix + 1, &f);

        if ((f & ~LONGINT_OVERFLOW) != LONGINT_OK) {
            *invalid = f;
            return 0;
        }

        if (ckd_mul(&result, n, o) || (result != 0 && ((e | f) & LONGINT_OVERFLOW))) {
            *invalid = LONGINT_OVERFLOW;
            return INTMAX_MAX;
        }

        if (result == 0 && STRPREFIX(str, "0x")) {
            diagnose(0, _("warning: %s is a zero multiplier; use %s if that is intended"),
                     quote_n(0, "0x"), quote_n(1, "00x"));
        }
        *invalid = LONGINT_OK;
        return result;
    }

    if (n <= INTMAX_MAX) {
        result = (intmax_t)n;
        *invalid = e;
        return result;
    }

    *invalid = LONGINT_OVERFLOW;
    return INTMAX_MAX;
}

/* OPERAND is of the form "X=...".  Return true if X is NAME.  */

ATTRIBUTE_PURE
static bool
operand_is (char const *operand, char const *name)
{
  return operand_matches (operand, name, '=');
}

static void scanargs(int argc, char *const *argv)
{
    idx_t blocksize = 0;
    intmax_t count = INTMAX_MAX;
    intmax_t skip = 0;
    intmax_t seek = 0;
    bool count_B = false, skip_B = false, seek_B = false;

    for (int i = optind; i < argc; i++) {
        const char *name = argv[i];
        const char *val = strchr(name, '=');

        if (!val) {
            diagnose(0, _("unrecognized operand %s"), quoteaf(name));
            usage(EXIT_FAILURE);
        }
        val++;

        if (operand_is(name, "if")) {
            input_file = val;
            continue;
        }
        if (operand_is(name, "of")) {
            output_file = val;
            continue;
        }
        if (operand_is(name, "conv")) {
            conversions_mask |= parse_symbols(val, conversions, false,
                                              N_("invalid conversion"));
            continue;
        }
        if (operand_is(name, "iflag")) {
            input_flags |= parse_symbols(val, flags, false,
                                         N_("invalid input flag"));
            continue;
        }
        if (operand_is(name, "oflag")) {
            output_flags |= parse_symbols(val, flags, false,
                                          N_("invalid output flag"));
            continue;
        }
        if (operand_is(name, "status")) {
            status_level = parse_symbols(val, statuses, true,
                                         N_("invalid status level"));
            continue;
        }

        strtol_error invalid = LONGINT_OK;
        intmax_t n = parse_integer(val, &invalid);
        bool has_B = strchr(val, 'B') != NULL;
        intmax_t n_min = 0, n_max = INTMAX_MAX;
        idx_t *converted_idx = NULL;
        idx_t max_blocksize = MIN(IDX_MAX - 1, MIN(SSIZE_MAX, OFF_T_MAX));

        if (operand_is(name, "ibs")) {
            n_min = 1;
            n_max = max_blocksize;
            converted_idx = &input_blocksize;
        } else if (operand_is(name, "obs")) {
            n_min = 1;
            n_max = max_blocksize;
            converted_idx = &output_blocksize;
        } else if (operand_is(name, "bs")) {
            n_min = 1;
            n_max = max_blocksize;
            converted_idx = &blocksize;
        } else if (operand_is(name, "cbs")) {
            n_min = 1;
            n_max = MIN(SIZE_MAX, IDX_MAX);
            converted_idx = &conversion_blocksize;
        } else if (operand_is(name, "skip") || operand_is(name, "iseek")) {
            skip = n;
            skip_B = has_B;
        } else if (operand_is(name + (*name == 'o'), "seek")) {
            seek = n;
            seek_B = has_B;
        } else if (operand_is(name, "count")) {
            count = n;
            count_B = has_B;
        } else {
            diagnose(0, _("unrecognized operand %s"), quoteaf(name));
            usage(EXIT_FAILURE);
        }

        if (n < n_min) {
            invalid = LONGINT_INVALID;
        } else if (n > n_max) {
            invalid = LONGINT_OVERFLOW;
        }

        if (invalid != LONGINT_OK) {
            error(EXIT_FAILURE, invalid == LONGINT_OVERFLOW ? EOVERFLOW : 0,
                  "%s: %s", _("invalid number"), quoteaf(val));
        } else if (converted_idx) {
            *converted_idx = n;
        }
    }

    if (blocksize) {
        input_blocksize = output_blocksize = blocksize;
    } else {
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

    if (output_flags & O_FULLBLOCK) {
        diagnose(0, "%s: %s", _("invalid output flag"), quote("fullblock"));
        usage(EXIT_FAILURE);
    }

    if (skip_B)
        input_flags |= O_SKIP_BYTES;
    if ((input_flags & O_SKIP_BYTES) && skip != 0) {
        skip_records = skip / input_blocksize;
        skip_bytes = skip % input_blocksize;
    } else if (skip != 0) {
        skip_records = skip;
    }

    if (count_B)
        input_flags |= O_COUNT_BYTES;
    if ((input_flags & O_COUNT_BYTES) && count != INTMAX_MAX) {
        max_records = count / input_blocksize;
        max_bytes = count % input_blocksize;
    } else if (count != INTMAX_MAX) {
        max_records = count;
    }

    if (seek_B)
        output_flags |= O_SEEK_BYTES;
    if ((output_flags & O_SEEK_BYTES) && seek != 0) {
        seek_records = seek / output_blocksize;
        seek_bytes = seek % output_blocksize;
    } else if (seek != 0) {
        seek_records = seek;
    }

    warn_partial_read =
        (!(conversions_mask & C_TWOBUFS) && !(input_flags & O_FULLBLOCK) &&
         (skip_records ||
          (max_records > 0 && max_records < INTMAX_MAX) ||
          ((input_flags | output_flags) & O_DIRECT)));

    iread_fnc = (input_flags & O_FULLBLOCK) ? iread_fullblock : iread;
    input_flags &= ~O_FULLBLOCK;

    if (multiple_bits_set(conversions_mask & (C_ASCII | C_EBCDIC | C_IBM)))
        error(EXIT_FAILURE, 0, _("cannot combine any two of {ascii,ebcdic,ibm}"));
    if (multiple_bits_set(conversions_mask & (C_BLOCK | C_UNBLOCK)))
        error(EXIT_FAILURE, 0, _("cannot combine block and unblock"));
    if (multiple_bits_set(conversions_mask & (C_LCASE | C_UCASE)))
        error(EXIT_FAILURE, 0, _("cannot combine lcase and ucase"));
    if (multiple_bits_set(conversions_mask & (C_EXCL | C_NOCREAT)))
        error(EXIT_FAILURE, 0, _("cannot combine excl and nocreat"));
    if (multiple_bits_set(input_flags & (O_DIRECT | O_NOCACHE)) ||
        multiple_bits_set(output_flags & (O_DIRECT | O_NOCACHE)))
        error(EXIT_FAILURE, 0, _("cannot combine direct and nocache"));

    if (input_flags & O_NOCACHE) {
        i_nocache = true;
        i_nocache_eof = (max_records == 0 && max_bytes == 0);
        input_flags &= ~O_NOCACHE;
    }
    if (output_flags & O_NOCACHE) {
        o_nocache = true;
        o_nocache_eof = (max_records == 0 && max_bytes == 0);
        output_flags &= ~O_NOCACHE;
    }
}

/* Fix up translation table. */

static void apply_translations(void)
{
    if (conversions_mask & C_ASCII) {
        translate_charset(ebcdic_to_ascii);
    }

    if (conversions_mask & C_UCASE || conversions_mask & C_LCASE) {
        int (*case_func)(int) = (conversions_mask & C_UCASE) ? toupper : tolower;
        for (int i = 0; i < 256; i++) {
            trans_table[i] = case_func(trans_table[i]);
        }
        translation_needed = true;
    }

    if (conversions_mask & C_EBCDIC) {
        translate_charset(ascii_to_ebcdic);
        newline_character = ascii_to_ebcdic['\n'];
        space_character = ascii_to_ebcdic[' '];
    } else if (conversions_mask & C_IBM) {
        translate_charset(ascii_to_ibm);
        newline_character = ascii_to_ibm['\n'];
        space_character = ascii_to_ibm[' '];
    }
}

/* Apply the character-set translations specified by the user
   to the NREAD bytes in BUF.  */

static void translate_buffer(char *buf, idx_t nread) {
    if (!buf || nread == 0)
        return;
    for (idx_t i = 0; i < nread; i++) {
        buf[i] = trans_table[to_uchar(buf[i])];
    }
}

/* Swap *NREAD bytes in BUF, which should have room for an extra byte
   after the end because the swapping is not in-place.  If *SAVED_BYTE
   is nonnegative, also swap that initial byte from the previous call.
   Save the last byte into into *SAVED_BYTE if needed to make the
   resulting *NREAD even, and set *SAVED_BYTE to -1 otherwise.
   Return the buffer's adjusted start, either BUF or BUF + 1.  */

static char *swab_buffer(char *buf, idx_t *nread, int *saved_byte)
{
    if (!buf || !nread || !saved_byte || *nread == 0)
        return buf;

    int prev_saved = *saved_byte;
    if (((prev_saved < 0) ? 1 : 0) == ((*nread & 1) ? 1 : 0)) {
        *nread -= 1;
        if (*nread < 0)
            *nread = 0;
        else
            *saved_byte = (unsigned char)buf[*nread];
    } else {
        *saved_byte = -1;
    }

    for (idx_t i = *nread; i > 1; i -= 2)
        buf[i] = buf[i - 2];

    if (prev_saved < 0)
        return buf + 1;

    buf[1] = (char)prev_saved;
    *nread += 1;
    return buf;
}

/* Add OFFSET to the input offset, setting the overflow flag if
   necessary.  */

static void advance_input_offset(intmax_t offset) {
    if (input_offset < 0) {
        return;
    }
    if (!ckd_add(&input_offset, input_offset, offset)) {
        return;
    }
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

static intmax_t skip(int fdesc, char const *file, intmax_t records, idx_t blocksize, idx_t *bytes)
{
    errno = 0;
    off_t offset;
    int use_lseek = 0;

    if (!ckd_mul(&offset, records, blocksize)
        && !ckd_add(&offset, offset, *bytes)
        && lseek(fdesc, offset, SEEK_CUR) >= 0)
    {
        use_lseek = 1;
    }

    if (use_lseek)
    {
        if (fdesc == STDIN_FILENO)
        {
            struct stat st;
            if (ifstat(STDIN_FILENO, &st) != 0)
                error(EXIT_FAILURE, errno, _("cannot fstat %s"), quoteaf(file));

            if (usable_st_size(&st) && st.st_size > 0 && input_offset >= 0 &&
                st.st_size - input_offset < offset)
            {
                records = (offset - st.st_size) / blocksize;
                offset = st.st_size - input_offset;
            }
            else
            {
                records = 0;
            }
            advance_input_offset(offset);
        }
        else
        {
            records = 0;
            *bytes = 0;
        }
        return records;
    }
    else
    {
        int lseek_errno = errno;
        if (lseek(fdesc, 0, SEEK_END) >= 0)
        {
            if (!lseek_errno)
                lseek_errno = EOVERFLOW;

            diagnose(
                lseek_errno,
                gettext(fdesc == STDIN_FILENO ?
                        N_("%s: cannot skip") :
                        N_("%s: cannot seek")),
                quotef(file)
            );
            quit(EXIT_FAILURE);
        }

        char *buf = NULL;
        if (fdesc == STDIN_FILENO)
        {
            alloc_ibuf();
            buf = ibuf;
        }
        else
        {
            alloc_obuf();
            buf = obuf;
        }

        while (records || *bytes)
        {
            ssize_t nread = iread_fnc(fdesc, buf, records ? blocksize : *bytes);
            if (nread < 0)
            {
                if (fdesc == STDIN_FILENO)
                {
                    diagnose(errno, _("error reading %s"), quoteaf(file));
                    if (conversions_mask & C_NOERROR)
                        print_stats();
                }
                else
                {
                    diagnose(lseek_errno, _("%s: cannot seek"), quotef(file));
                }
                quit(EXIT_FAILURE);
            }
            if (nread == 0)
                break;
            if (fdesc == STDIN_FILENO)
                advance_input_offset(nread);

            if (records != 0)
                records--;
            else
                *bytes = 0;
        }
        return records;
    }
}


/* Advance the input by NBYTES if possible, after a read error.
   The input file offset may or may not have advanced after the failed
   read; adjust it to point just after the bad record regardless.
   Return true if successful, or if the input is already known to not
   be seekable.  */

static bool advance_input_after_read_error(idx_t nbytes) {
    if (!input_seekable) {
        if (input_seek_errno == ESPIPE)
            return true;
        errno = input_seek_errno;
        diagnose(errno, _("%s: cannot seek"), quotef(input_file));
        return false;
    }

    advance_input_offset(nbytes);

    if (input_offset < 0) {
        diagnose(0, _("offset overflow while reading file %s"), quoteaf(input_file));
        return false;
    }

    off_t offset = lseek(STDIN_FILENO, 0, SEEK_CUR);
    if (offset < 0) {
        diagnose(errno, _("%s: cannot seek"), quotef(input_file));
        return false;
    }

    if (offset == input_offset)
        return true;

    off_t diff = input_offset - offset;
    if (!(0 <= diff && diff <= nbytes) && status_level != STATUS_NONE)
        diagnose(0, _("warning: invalid file offset after failed read"));

    if (lseek(STDIN_FILENO, diff, SEEK_CUR) >= 0)
        return true;

    if (errno == 0)
        diagnose(0, _("cannot work around kernel bug after all"));

    diagnose(errno, _("%s: cannot seek"), quotef(input_file));
    return false;
}

/* Copy NREAD bytes of BUF, with no conversions.  */

static void copy_simple(const char *buf, idx_t nread) {
    while (nread > 0) {
        idx_t nfree = MIN(nread, output_blocksize - oc);
        memcpy(obuf + oc, buf, nfree);
        nread -= nfree;
        buf += nfree;
        oc += nfree;
        if (oc >= output_blocksize) {
            write_output();
        }
    }
}

/* Copy NREAD bytes of BUF, doing conv=block
   (pad newline-terminated records to 'conversion_blocksize',
   replacing the newline with trailing spaces).  */

static void copy_with_block(const char *buf, idx_t nread) {
    if (!buf) {
        return;
    }
    for (idx_t i = 0; i < nread; i++) {
        if (buf[i] == newline_character) {
            if (col < conversion_blocksize) {
                for (idx_t j = col; j < conversion_blocksize; j++) {
                    output_char(space_character);
                }
            }
            col = 0;
        } else {
            if (col < conversion_blocksize) {
                output_char(buf[i]);
            } else if (col == conversion_blocksize) {
                r_truncate++;
            }
            col++;
        }
    }
}

/* Copy NREAD bytes of BUF, doing conv=unblock
   (replace trailing spaces in 'conversion_blocksize'-sized records
   with a newline).  */

static void copy_with_unblock(const char *buf, idx_t nread)
{
    static idx_t pending_spaces = 0;

    idx_t i = 0;
    while (i < nread)
    {
        char c = buf[i];

        if (col >= conversion_blocksize)
        {
            col = 0;
            pending_spaces = 0;
            output_char(newline_character);
            continue;
        }
        if (c == space_character)
        {
            pending_spaces++;
        }
        else
        {
            for (; pending_spaces > 0; pending_spaces--)
            {
                output_char(space_character);
                col++;
                if (col >= conversion_blocksize)
                {
                    col = 0;
                    output_char(newline_character);
                }
            }
            output_char(c);
            col++;
        }
        i++;
    }
}

/* Set the file descriptor flags for FD that correspond to the nonzero bits
   in ADD_FLAGS.  The file's name is NAME.  */

static void set_fd_flags(int fd, int add_flags, char const *name)
{
    add_flags &= ~(O_NOCTTY | O_NOFOLLOW);

    if (add_flags == 0)
        return;

    int old_flags = fcntl(fd, F_GETFL);
    if (old_flags < 0)
        error(EXIT_FAILURE, errno, _("getting flags for %s"), quoteaf(name));

    int new_flags = old_flags | add_flags;

    if (old_flags == new_flags)
        return;

    int temp_flags = new_flags;
    if (temp_flags & (O_DIRECTORY | O_NOLINKS))
    {
        struct stat st;
        if (ifstat(fd, &st) != 0)
            error(EXIT_FAILURE, errno, _("stat failed on %s"), quoteaf(name));

        if ((temp_flags & O_DIRECTORY) && !S_ISDIR(st.st_mode))
        {
            errno = ENOTDIR;
            error(EXIT_FAILURE, errno, _("not a directory: %s"), quoteaf(name));
        }
        if ((temp_flags & O_NOLINKS) && st.st_nlink > 1)
        {
            errno = EMLINK;
            error(EXIT_FAILURE, errno, _("too many links: %s"), quoteaf(name));
        }
        new_flags &= ~(O_DIRECTORY | O_NOLINKS);
    }

    if (old_flags != new_flags)
    {
        if (fcntl(fd, F_SETFL, new_flags) == -1)
            error(EXIT_FAILURE, errno, _("setting flags for %s"), quoteaf(name));
    }
}

/* The main loop.  */

static int dd_copy(void)
{
    char *bufstart;
    ssize_t nread;
    idx_t partread = 0;
    int exit_status = EXIT_SUCCESS;
    idx_t n_bytes_read;
    int saved_byte = -1;

    if (skip_records != 0 || skip_bytes != 0) {
        intmax_t us_bytes;
        bool us_bytes_overflow =
            (ckd_mul(&us_bytes, skip_records, input_blocksize) ||
             ckd_add(&us_bytes, skip_bytes, us_bytes));
        off_t input_offset0 = input_offset;
        intmax_t us_blocks = skip(STDIN_FILENO, input_file, skip_records, input_blocksize, &skip_bytes);

        if ((us_blocks ||
             (0 <= input_offset &&
              (us_bytes_overflow ||
               us_bytes != input_offset - input_offset0)))
            && status_level != STATUS_NONE) {
            diagnose(0, _("%s: cannot skip to specified offset"), quotef(input_file));
        }
    }

    if (seek_records != 0 || seek_bytes != 0) {
        idx_t bytes = seek_bytes;
        intmax_t write_records = skip(STDOUT_FILENO, output_file, seek_records, output_blocksize, &bytes);

        if (write_records != 0 || bytes != 0) {
            memset(obuf, 0, write_records ? output_blocksize : bytes);
            do {
                idx_t size = write_records ? output_blocksize : bytes;
                if (iwrite(STDOUT_FILENO, obuf, size) != size) {
                    diagnose(errno, _("writing to %s"), quoteaf(output_file));
                    quit(EXIT_FAILURE);
                }
                if (write_records != 0)
                    write_records--;
                else
                    bytes = 0;
            } while (write_records || bytes);
        }
    }

    if (max_records == 0 && max_bytes == 0)
        return exit_status;

    alloc_ibuf();
    alloc_obuf();

    while (true) {
        if (status_level == STATUS_PROGRESS) {
            xtime_t progress_time = gethrxtime();
            if (next_time <= progress_time) {
                print_xfer_stats(progress_time);
                next_time += XTIME_PRECISION;
            }
        }

        if (r_partial + r_full >= max_records + !!max_bytes)
            break;

        if ((conversions_mask & C_SYNC) && (conversions_mask & C_NOERROR))
            memset(ibuf, (conversions_mask & (C_BLOCK | C_UNBLOCK)) ? ' ' : '\0', input_blocksize);

        if (r_partial + r_full >= max_records)
            nread = iread_fnc(STDIN_FILENO, ibuf, max_bytes);
        else
            nread = iread_fnc(STDIN_FILENO, ibuf, input_blocksize);

        if (nread > 0) {
            advance_input_offset(nread);
            if (i_nocache)
                invalidate_cache(STDIN_FILENO, nread);
        } else if (nread == 0) {
            i_nocache_eof |= i_nocache;
            o_nocache_eof |= o_nocache && !(conversions_mask & C_NOTRUNC);
            break;
        } else {
            if (!(conversions_mask & C_NOERROR) || status_level != STATUS_NONE)
                diagnose(errno, _("error reading %s"), quoteaf(input_file));

            if (conversions_mask & C_NOERROR) {
                print_stats();
                idx_t bad_portion = input_blocksize - partread;
                invalidate_cache(STDIN_FILENO, bad_portion);

                if (!advance_input_after_read_error(bad_portion)) {
                    exit_status = EXIT_FAILURE;
                    input_seekable = false;
                    input_seek_errno = ESPIPE;
                }
                if ((conversions_mask & C_SYNC) && !partread)
                    nread = 0;
                else
                    continue;
            } else {
                exit_status = EXIT_FAILURE;
                break;
            }
        }

        n_bytes_read = nread;

        if (n_bytes_read < input_blocksize) {
            r_partial++;
            partread = n_bytes_read;
            if (conversions_mask & C_SYNC) {
                if (!(conversions_mask & C_NOERROR))
                    memset(ibuf + n_bytes_read,
                           (conversions_mask & (C_BLOCK | C_UNBLOCK)) ? ' ' : '\0',
                           input_blocksize - n_bytes_read);
                n_bytes_read = input_blocksize;
            }
        } else {
            r_full++;
            partread = 0;
        }

        if (ibuf == obuf) {
            idx_t nwritten = iwrite(STDOUT_FILENO, obuf, n_bytes_read);
            w_bytes += nwritten;
            if (nwritten != n_bytes_read) {
                diagnose(errno, _("error writing %s"), quoteaf(output_file));
                return EXIT_FAILURE;
            } else if (n_bytes_read == input_blocksize)
                w_full++;
            else
                w_partial++;
            continue;
        }

        if (translation_needed)
            translate_buffer(ibuf, n_bytes_read);

        if (conversions_mask & C_SWAB)
            bufstart = swab_buffer(ibuf, &n_bytes_read, &saved_byte);
        else
            bufstart = ibuf;

        if (conversions_mask & C_BLOCK)
            copy_with_block(bufstart, n_bytes_read);
        else if (conversions_mask & C_UNBLOCK)
            copy_with_unblock(bufstart, n_bytes_read);
        else
            copy_simple(bufstart, n_bytes_read);
    }

    if (0 <= saved_byte) {
        char saved_char = saved_byte;
        if (conversions_mask & C_BLOCK)
            copy_with_block(&saved_char, 1);
        else if (conversions_mask & C_UNBLOCK)
            copy_with_unblock(&saved_char, 1);
        else
            output_char(saved_char);
    }

    if ((conversions_mask & C_BLOCK) && col > 0) {
        for (idx_t i = col; i < conversion_blocksize; i++)
            output_char(space_character);
    }

    if (col && (conversions_mask & C_UNBLOCK)) {
        output_char(newline_character);
    }

    if (oc != 0) {
        idx_t nwritten = iwrite(STDOUT_FILENO, obuf, oc);
        w_bytes += nwritten;
        if (nwritten != 0)
            w_partial++;
        if (nwritten != oc) {
            diagnose(errno, _("error writing %s"), quoteaf(output_file));
            return EXIT_FAILURE;
        }
    }

    if (final_op_was_seek) {
        struct stat stdout_stat;
        if (ifstat(STDOUT_FILENO, &stdout_stat) != 0) {
            diagnose(errno, _("cannot fstat %s"), quoteaf(output_file));
            return EXIT_FAILURE;
        }
        if (S_ISREG(stdout_stat.st_mode) || S_TYPEISSHM(&stdout_stat)) {
            off_t output_offset = lseek(STDOUT_FILENO, 0, SEEK_CUR);
            if (0 <= output_offset && stdout_stat.st_size < output_offset) {
                if (iftruncate(STDOUT_FILENO, output_offset) != 0) {
                    diagnose(errno, _("failed to truncate to %jd bytes"
                        " in output file %s"),
                        (intmax_t)output_offset, quoteaf(output_file));
                    return EXIT_FAILURE;
                }
            }
        }
    }

    if ((conversions_mask & (C_FDATASYNC | C_FSYNC))
        && status_level == STATUS_PROGRESS
        && 0 <= reported_w_bytes && reported_w_bytes < w_bytes)
        print_xfer_stats(0);

    return exit_status;
}


/* Synchronize output according to conversions_mask.
   Do this even if w_bytes is zero, as fsync and fdatasync
   flush out write requests from other processes too.
   Clear bits in conversions_mask so that synchronization is done only once.
   Return zero if successful, an exit status otherwise.  */

static int synchronize_output(void)
{
    int exit_status = 0;
    int mask = conversions_mask;
    conversions_mask &= ~(C_FDATASYNC | C_FSYNC);

    if ((mask & C_FDATASYNC)) {
        if (ifdatasync(STDOUT_FILENO) != 0) {
            if (errno != ENOSYS && errno != EINVAL) {
                diagnose(errno, _("fdatasync failed for %s"), quoteaf(output_file));
                exit_status = EXIT_FAILURE;
            }
            mask |= C_FSYNC;
        }
    }

    if ((mask & C_FSYNC)) {
        if (ifsync(STDOUT_FILENO) != 0) {
            diagnose(errno, _("fsync failed for %s"), quoteaf(output_file));
            return EXIT_FAILURE;
        }
    }

    return exit_status;
}

int main(int argc, char **argv)
{
    int i;
    int exit_status = EXIT_SUCCESS;
    off_t offset;

    install_signal_handlers();

    initialize_main(&argc, &argv);
    set_program_name(argv[0]);
    setlocale(LC_ALL, "");
    bindtextdomain(PACKAGE, LOCALEDIR);
    textdomain(PACKAGE);

    if (atexit(maybe_close_stdout) != 0)
        error(EXIT_FAILURE, 0, _("atexit failed"));

    page_size = getpagesize();

    parse_gnu_standard_options_only(argc, argv, PROGRAM_NAME, PACKAGE, Version,
                                   true, usage, AUTHORS, (char const *) nullptr);
    close_stdout_required = false;

    for (i = 0; i < 256; i++)
        trans_table[i] = i;

    scanargs(argc, argv);

    apply_translations();

    if (input_file == nullptr)
    {
        input_file = _("standard input");
        set_fd_flags(STDIN_FILENO, input_flags, input_file);
    }
    else
    {
        if (ifd_reopen(STDIN_FILENO, input_file, O_RDONLY | input_flags, 0) < 0)
            error(EXIT_FAILURE, errno, _("failed to open %s"), quoteaf(input_file));
    }

    offset = lseek(STDIN_FILENO, 0, SEEK_CUR);
    input_seekable = (offset >= 0);
    input_offset = (offset >= 0) ? offset : 0;
    input_seek_errno = errno;

    if (output_file == nullptr)
    {
        output_file = _("standard output");
        set_fd_flags(STDOUT_FILENO, output_flags, output_file);
    }
    else
    {
        mode_t perms = MODE_RW_UGO;
        int opts = output_flags
                   | ((conversions_mask & C_NOCREAT) ? 0 : O_CREAT)
                   | ((conversions_mask & C_EXCL) ? O_EXCL : 0)
                   | ((seek_records || (conversions_mask & C_NOTRUNC)) ? 0 : O_TRUNC);

        off_t size;
        bool truncation_needed = !(conversions_mask & C_NOTRUNC);

        if ((ckd_mul(&size, seek_records, output_blocksize) || ckd_add(&size, seek_bytes, size)) && truncation_needed)
        {
            error(EXIT_FAILURE, 0,
                  _("offset too large: cannot truncate to a length of seek=%jd (%td-byte) blocks"),
                  seek_records, output_blocksize);
        }

        int output_fd = -1;
        if (seek_records == 0 || ifd_reopen(STDOUT_FILENO, output_file, O_RDWR | opts, perms) < 0)
        {
            if (ifd_reopen(STDOUT_FILENO, output_file, O_WRONLY | opts, perms) < 0)
                error(EXIT_FAILURE, errno, _("failed to open %s"), quoteaf(output_file));
        }

        if (seek_records != 0 && truncation_needed)
        {
            if (iftruncate(STDOUT_FILENO, size) != 0)
            {
                int ftruncate_errno = errno;
                struct stat stdout_stat;
                if (ifstat(STDOUT_FILENO, &stdout_stat) != 0)
                {
                    diagnose(errno, _("cannot fstat %s"), quoteaf(output_file));
                    exit_status = EXIT_FAILURE;
                }
                else if (S_ISREG(stdout_stat.st_mode) || S_ISDIR(stdout_stat.st_mode) || S_TYPEISSHM(&stdout_stat))
                {
                    intmax_t isize = size;
                    diagnose(ftruncate_errno,
                             _("failed to truncate to %jd bytes in output file %s"),
                             isize, quoteaf(output_file));
                    exit_status = EXIT_FAILURE;
                }
            }
        }
    }

    start_time = gethrxtime();
    next_time = start_time + XTIME_PRECISION;

    exit_status = dd_copy();

    int sync_status = synchronize_output();
    if (sync_status != 0)
        exit_status = sync_status;

    if (max_records == 0 && max_bytes == 0)
    {
        if (i_nocache && !invalidate_cache(STDIN_FILENO, 0))
        {
            diagnose(errno, _("failed to discard cache for: %s"), quotef(input_file));
            exit_status = EXIT_FAILURE;
        }
        if (o_nocache && !invalidate_cache(STDOUT_FILENO, 0))
        {
            diagnose(errno, _("failed to discard cache for: %s"), quotef(output_file));
            exit_status = EXIT_FAILURE;
        }
    }
    else
    {
        if (i_nocache || i_nocache_eof)
            invalidate_cache(STDIN_FILENO, 0);
        if (o_nocache || o_nocache_eof)
            invalidate_cache(STDOUT_FILENO, 0);
    }

    finish_up();
    main_exit(exit_status);
}
