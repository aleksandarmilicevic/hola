#!/bin/bash

f=$1

if [[ -z $f ]]; then
  f="max-4"
fi

pygmentize -l alloy -f html -o $f.html $f.als; 
echo '<!DOCTYPE html><html><head><link rel="stylesheet" type="text/css" href="../../../css/alloy.css"/></head><body>' > tmp.html
cat $f.html >> tmp.html
echo "</body></html>" >> tmp.html

mv tmp.html $f.als.html
