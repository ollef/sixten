#!/bin/bash

set -e
set -u

stack ${STACK_FLAGS-} install

for file in $(find ./tests/success -name "*.vix" | sort)
do
  if [ -f "$file-expected" ]
  then
    sixten test "$file" --expected "$file-expected" "$@"
  else
    sixten test "$file" "$@"
  fi
done

for dir in $(find ./tests/success-multi -type d | sort)
do
  files=$(find "$dir" -maxdepth 1 -name "*.vix" | sort)
  if [ -n "$files" ]
  then
    expectedFile=""
    for file in $(find "$dir" -maxdepth 1 -name "*-expected")
    do
      expectedFile="$file"
      break
    done

    if [ -n "$expectedFile" ]
    then
      sixten test $files --expected $expectedFile "$@"
    else
      sixten test $files "$@"
    fi
  fi
done

for file in $(find ./tests/syntax-error -name "*.vix" | sort)
do
  sixten test "$file" --expect-syntax-error "$@"
done

for file in $(find ./tests/type-error -name "*.vix" | sort)
do
  sixten test "$file" --expect-type-error "$@"
done

for dir in $(find ./tests/type-error-multi -type d | sort)
do
  files=$(find "$dir" -maxdepth 1 -name "*.vix" | sort)
  if [ -n "$files" ]
  then
    sixten test $files --expect-type-error "$@"
  fi
done
