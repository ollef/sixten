#!/bin/bash

set -e
set -u

stack install


for file in $(find ./tests/success -name "*.vix" | sort)
do
  if [ -f $file-expected ];
  then
    sixten test $file --expected $file-expected "$@"
  else
    sixten test $file "$@"
  fi
done

for file in $(find ./tests/syntax-error -name "*.vix" | sort)
do
  sixten test $file --expect-syntax-error "$@"
done

for file in $(find ./tests/type-error -name "*.vix" | sort)
do
  sixten test $file --expect-type-error "$@"
done
