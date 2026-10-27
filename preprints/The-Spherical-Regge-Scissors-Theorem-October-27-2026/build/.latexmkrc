# Fix the PDF build clock so clean builds of unchanged sources are
# byte-for-byte reproducible with the recorded TeX toolchain. The epoch is
# 2026-09-27 00:00:00 UTC, the fixed date for this release candidate.
$ENV{'SOURCE_DATE_EPOCH'} = '1790467200';
$ENV{'FORCE_SOURCE_DATE'} = '1';
$ENV{'TZ'} = 'UTC';
