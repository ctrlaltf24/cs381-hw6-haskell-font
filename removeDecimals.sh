#!/bin/bash
ls letters | while read line
do
    cat letters/$line | sed -E 's/\.[0-9]+//g' | tee letters_clean/$line > /dev/null
done