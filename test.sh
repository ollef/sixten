#!/bin/bash

set -e
set -u

stack install

for file in tests/success/*.vix
do
  if [ -f $file-expected ];
  then
    sixten test $file --expected $file-expected "$@"
  else
    sixten test $file "$@"
  fi
done

for file in tests/syntax-error/*.vix
do
  sixten test $file --expect-syntax-error "$@"
done

for file in tests/type-error/*.vix
do
  sixten test $file --expect-type-error "$@"
done
