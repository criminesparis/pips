#! /usr/bin/perl -w
#
# $Id: tspear-build-xml.pl 23412 2017-08-09 15:07:09Z irigoin $
#
# build XML application from box and task databases
# usage: $0 box-db task-db includes main
#

use strict;

sub log_misc($$)
{
  my ($level, $message) = @_;
  print STDERR
    "<$level>\n" .
    "  <Description Message=\"$message\" />\n" .
    "</$level>\n";
}

# Status: (OK|ABORT|TIMEOUT|INTERNAL_ERROR|USER_ERROR|ERROR)
sub log_exit($$$)
{
  my ($code, $status, $message) = @_;
  print STDERR
    "<Exit Code=\"$code\" Status=\"$status\" Source=\"tspear-build-xml.pl\">\n" .
    "  <Description Message=\"$message\" />\n" .
    "</Exit>\n";
}

log_exit(120, 'INTERNAL_ERROR', 'expecting 4 arguments') unless @ARGV == 4;

my ($box, $task, $includes, $main) = @ARGV;
my ($boxdb, $taskdb) = ("$box.database", "$task.database");

# tell file module_status (not found, box or task)
sub module_status($$)
{
  my ($filename, $func) = @_;
  if (! -e $filename) {
    log_misc('Information', "no XML for module '$func'");
    return 0;
  }
  open(my $fh, '<', $filename)
    or log_exit(121, 'ERROR', "cannot open '$filename'");
  my $first = <$fh>;
  close($fh);
  return 1 if $first =~ /XML prettyprint for box "/;
  return 2 if $first =~ /XML prettyprint for task "/;
  log_exit(122, 'ERROR', "missing comment header '$filename'");
}

# show XML
my %xml_done = ();
my @xml_gen = ();
sub cat_xml
{
  my ($func, $must) = @_;
  $xml_done{$func} = 1;
  my $bfile = "$boxdb/$func/$func.xml";
  my $tfile = "$taskdb/$func/$func.xml";
  # check taskdb first, because in box db some simplifications may
  # have switch tasks into boxes.
  my $file = ("$taskdb" && -e $tfile) ? $tfile: $bfile;
  my $status = module_status($file, $func);
  # silently ignored if not found...
  log_exit(123, 'ERROR', "no XML for $func") if $must and not $status;
  return if $status == 0;
  if ($status == 2) {
    if ("$taskdb" and -e $tfile) {
      $file = $tfile;
      log_misc('Information', "using task XML for task $func");
    }
    else {
      $file = $bfile;
      log_misc('Information', "using box XML for task $func");
    }
  }
  else
  {
    $file = $bfile;
    log_misc('Information', "using box XML for box $func");
  }
  open(my $fh, '<', $file)
    or log_exit(124, 'ERROR', "cannot open XML printed file '$file'");
  push @xml_gen, $func;
  my @todo = ();
  while (<$fh>) {
    if ($status == 1 and /<Call Name="(\w+)"/) {
      push @todo, $1;
    }
    print;
  }
  close($fh);
  for my $called (sort @todo) {
    if (not exists $xml_done{$called}) {
      cat_xml($called, 0);
    }
  }
}

my $appfile = "$boxdb/$main/$main.app.xml";
open(APP, '<', $appfile)
  or log_exit(125, 'ERROR', "cannot open XML application '$appfile'");
while (<APP>) {
  if (/<!-- Main Box -->/) {
    cat_xml($main, 1);
  }
  elsif (/<!-- Included Files -->/) {
    if (-e $includes) {
      print "  <IncludedFiles>\n";
      open(my $ifh, '<', $includes)
         or log_exit(126, 'ERROR', "cannot open include file list '$includes'");
      while (my $inc = <$ifh>) {
	chomp $inc;
	print "    <File Name=\"$inc\" />\n";
      }
      close($ifh);
      print "  </IncludedFiles>\n";
    }
    else {
      print "  <IncludedFiles/>\n";
    }
  }
  else {
    print;
  }
}
close(APP);

print "<!-- boxes & tasks: @xml_gen -->\n";

log_exit(0, 'OK', 'application generation done');
