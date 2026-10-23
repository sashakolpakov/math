# Fix the PDF clock; the manuscript date is explicit in its TeX source.
$ENV{'SOURCE_DATE_EPOCH'} = '1792713600';
$ENV{'FORCE_SOURCE_DATE'} = '1';
$ENV{'TZ'} = 'UTC';
