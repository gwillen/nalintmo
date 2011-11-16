#!/usr/bin/perl

use strict;
use warnings;

# We will implement our various exp constructors as follows:
# - Num: scalar ref blessed as Num
# - Sym: scalar ref blessed as Sym
# - Cons: list ref
# - Nil: list ref
# - Func: sub ref

sub Num($) {
  my ($n) = @_;
  return bless \$n, Num;
}

sub Sym($) {
  my ($s) = @_;
  return bless \$s, Sym;
}

our %global_env = {};

sub to_string($) {
  my ($e) = @_;
  if (ref $e eq "Sym") { return $$e; }
  if (ref $e eq "Num") { return "".$$e; }
  if (ref $e eq "CODE") { return "<function>"; }
  if (ref $e eq "ARRAY") {
    return "(" .
           join(" ", (map { to_string($_) } @$e)) .
           ")";
  }
  if (ref $e eq "HASH") {
    return "{" .
           join(", ",
                map { to_string($_) . "->" . to_string($e->{$_}) } keys %$e) .
           "}";
  }
  die("Bad sexp: " . $e);  # Can't use fail here, recursion
}

sub fail($$) {
  my ($msg, $e) = @_;
  $msg .= to_string($e);
  die($msg . "; died");
}

# Contexts are arrays of hashes as in the Pike version
sub env_has($$) {
  my ($ctx, $key) = @_;
  if (ref $key ne "Sym") { fail("Bad key: ", $key); }
  $k = $$key;

  if (scalar @$ctx == 0) { return 0; }
  if (exists $ctx->[0]{$k}) { return 1; }
  my @rest = @$ctx;
  shift @rest;
  return env_has(\@rest, $key);
}

sub env_get($$) {
  my ($ctx, $key) = @_;
  if (ref $key ne "Sym") { fail("Bad key: ", $key); }
  $k = $$key;

  if (scalar @$ctx == 0) { fail("Not found in environment: ", $key); }
  if (exists $ctx->[0]{$k}) { return $ctx->[0]{$k}; }
  my @rest = @$ctx;
  shift @rest;
  return env_get(\@rest, $key);
}

sub env_set($$$) {
  my ($ctx, $key, $value) = @_;
  if (ref $key ne "Sym") { fail("Bad key: ", $key); }
  $k = $$key;

  if (scalar @$ctx == 0) { fail("Not found in environment: ", $key); }
  if (exists $ctx->[0]{$k}) { $ctx->[0]{$k} = $value; return; }
  my @rest = @$ctx;
  shift @rest;
  env_set(\@rest, $key, $value);
}

sub ctx_lookup($$) {
  my ($ctx, $key) = @_;
  if (env_has($ctx, $key)) { return env_get($ctx, $key); }
  if (exists $global_env{$key}) { return $global_env{$key}; }
  fail("Not found in environment: ", $key);
}

sub ctx_mutate($$$) {
  my ($ctx, $key, $val) = @_;
  if (env_has($ctx, $key)) { env_set($ctx, $key, $val); return; }
  if (exists $global_env{$key}) { $global_env{$key} = $val; return; }
  fail("Not found in envirionment: ", $key);
}

sub extend_ctx($$$) {
  my ($ctx, $params, $args) = @_;

  if (ref $params ne "ARRAY" || ref $args ne "ARRAY") {
    fail("Non-arrays passed to extend_ctx: ", $args);  # XXX bad error
  }
  if (scalar @$params != scalar @$args) {
    fail("Param/arg count mismatch: ", $args);  # XXX bad error
  }
  my %new_map = ();
  for my $i (0 .. $#{$params}) {
    $new_map{$params->[$i]} = $args->[$i];
  }
  my $new_ctx = [\%new_map, @$ctx];
  return $new_ctx;
}

sub do_cond($$) {
  my ($ctx, $clauses) = @_;

  if (scalar @$clauses == 0) { return []; }
  my @rest = @$clauses;
  my $clause = shift @rest;
  if (ref $clause ne "ARRAY" || scalar @$clause == 0) {
    fail("Clause of cond must be list: ", $clause);
  }
  my $truth = eval($ctx, $clause->[0]);
  if (ref $truth eq "ARRAY" && scalar @$truth == 0) {
    return do_cond($ctx, \@rest);
  }
  if (scalar @$clause == 1) { return $truth; }
  my @results = @$clause;
  $results[0] = Sym("progn");
  return eval($ctx, \@results);
  die("Unimplemented");
}

sub do_eval($$) {
  my ($ctx, $e) = @_;
  print "Evaluating " . (to_string $e) . " in ctx " . (to_string $ctx) . "; " .  (to_string $global_env) . "\n";

  if (ref $e eq "Num") { return $e; }
  if (ref $e eq "Sym") { return env_lookup($ctx, $e); }
  if (ref $e eq "ARRAY") {
    if (scalar @$e == 0) { return $e; }
    my @tl = @$e;
    my $hd = shift @tl;
    if ($hd eq "progn") {
      if (scalar @tl == 0) { return []; }
      my @results = map { do_eval($ctx, $_); } @tl;
      return $results[-1];
    }
    if ($hd eq "quote") {
      scalar @tl == 1 or fail("Quote applied wrong number of args in exp: ", $e);
      return $tl[0];
    }
    if ($hd eq "lambda") {
      ref $tl[0] eq "ARRAY" or fail("Lambda arglist not array in exp: ", $e);
      my @params = @{$tl[0]};
      my @body = @tl;
      $body[0] = Sym("progn");
      return sub(@) {
        $newctx = extend_ctx($ctx, \@params, \@_);
        return do_eval($newctx, $body);
      };
    }
    if ($hd eq "define") {
      my ($name, $value);
      if (ref $tl[0] eq "Sym") {
        scalar @tl == 2 or fail("Define of symbol with wrong number of args in exp: ", $e);
        $name = $tl[0];
        $value = do_eval($ctx, $tl[1]);
      } elsif (ref $tl[0] eq "ARRAY") {
        scalar @{$tl[0]} != 0 or fail("Define of nil: ", $e);
        $name = $tl[0][0];
        my @params = @{$tl[0]};
        shift @params;
        my @body = @tl;
        $body[0] = Sym("progn");
        $value = sub(@) {
          $newctx = extend_ctx($ctx, \@params, \@_);
          return do_eval($newctx, $body);
        };
      } else { fail("Bad define: ", $e); }
      global_env{$name} = $value;
      return value;
    }
    if ($hd eq "setq") {
      if (scalar @tl != 2) { fail("Setq applied to wrong number of args in exp: ", $e); }
      my $val = do_eval($ctx, $tail[1]);
      ctx_mutate($ctx, $tail[0], $val);
      return $val;
    }
    if ($hd eq "cond") {
      return do_cond($ctx, \@tail);
    }
    # Function application
    my $f = do_eval($ctx, $hd);
    my @args = map { do_eval($ctx, $_) } @tail;
    return $f->(@args);
  }
  fail("No case in eval for: ", $e);
}

sub do_car($@) {
  scalar @_ == 1 or fail("Car applied to wrong number of args: ", \@_);
  ref $_[0] eq "ARRAY" or fail("Car applied to non-cons: ", $_[0]);
  scalar @{$_[0]} > 0 or fail("Car applied to nil: ", $_[0]);
  return $_[0][0];
}

sub do_cdr(@) {
  scalar @_ == 1 or fail("Cdr applied to wrong number of args: ", \@_);
  ref $_[0] eq "ARRAY" or fail("Cdr applied to non-cons: ", $_[0]);
  scalar @{$_[0]} > 0 or fail("Cdr applied to nil: ", $_[0]);
  my @contents = @{$_[0]};
  shift @contents;
  return \@contents;
}

sub do_cons(@) {
  scalar @_ == 2 or fail("Cons applied to wrong number of args: ", \@_);
  ref $_[1] eq "ARRAY" or fail("Second arg to cons is non-cons: ", \@_);
  return [$_[0], @{$_[1]}];
}

sub do_eq(@) {
  scalar @_ == 2 or fail("Eq applied to wrong number of args: ", \@_);
  if (ref $_[0] eq "Num" && ref $_[1] eq "Num") {
    return ${$_[0]} == ${$_[1]} or [];
  }
  if (ref $_[0] eq "Sym" && ref $_[1] eq "Sym") {
    return ${$_[0]} eq ${$_[1]} or [];
  }
  if (ref $_[0] eq "ARRAY" && ref $_[1] eq "ARRAY") {
    return (scalar @{$_[0]} == 0 &&
            scalar @{$_[1]} == 0) or [];
  }
  return []; # No deep comparison.
}

sub do_plus(@) {
  my $result = 0;
  map {
    ref $_ eq "Num" or fail("Non-numeric argument to plus: ", $_);
    $result += $$_;
  } @_;
  return Num($result);
}

sub do_minus(@) {
  scalar @_ > 0 or fail("Not enough arguments to minus: ", \@_);
  ref $_[0] eq "Num" or fail("Non-numeric argument to minus: ", $_[0]);
  if (scalar @_ == 1) { return Num(- ${$_[0]}); }
  my $result = ${$_[0]};
  shift @_;
  map {
    ref $_ eq "Num" or fail("Non-numeric argument to minus: ", $_);
    $result -= $$_;
  } @_;
  return Num($result);
}

sub do_times(@) {
  my $result = 1;
  map {
    ref $_ eq "Num" or fail("Non-numeric argument to times: ", $_);
    $result *= $$_;
  } @_;
  return Num($result);
}

$global_env{"car"} = \&do_car;
$global_env{"cdr"} = \&do_cdr;
$global_env{"cons"} = \&do_cons;
$global_env{"eq"} = \&do_eq;
$global_env{"+"} = \&do_plus;
$global_env{"-"} = \&do_minus;
$global_env{"*"} = \&do_times;

$fact_test =
[Sym "progn",
  [Sym "define", [Sym "fact", Sym "n"],
    [Sym "cond",
      [[Sym "eq", Sym "n", Num 0], Num 1],
      [Num 1, [Sym "*", Sym "n", [Sym "fact", [Sym "-", Sym "n", Num 1]]]]]],
  [Sym "fact", Num 5]];

print to_string(do_eval([], $fact_test)) . "\n";

exit 0;
