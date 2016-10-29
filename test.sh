#!/bin/bash

set -e
set -u

stack install
for file in tests/*.vix
do
  sixten test $file --expected $file-expected
done
