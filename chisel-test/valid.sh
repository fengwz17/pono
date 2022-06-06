#!/bin/bash

function read_dir() {
echo "" > time.log
for file in `ls $1`
    do
        if [ -d $1"/"$file ]
        then
            read_dir $1"/"$file
        else
            # echo $1"/"$file
            check_suffix $1"/"$file
        fi
    done
} 



check_suffix()
{
    file=$1

    if [ "${file##*.}" = "btor" ] || [ "${file##*.}" = "btor2" ] || [ "${file##*.}" = "vmt" ]; then
        echo $file
        
        START_TIME=$[$(date +%s%N)/1000000]
        # python3 avr_pr.py -w workers.txt $file > btorOutput/${file##*\/}.log
        ./pono -e ic3backbits -v 1 -k 100 $file > results/${file##*\/}.log
        END_TIME=$[$(date +%s%N)/1000000]
        EXECUTE_TIME=$[$END_TIME-$START_TIME]
        
        echo "scale=2;$EXECUTE_TIME/1000" | bc >> time.log
        # echo "btorOutput/${file##*\/}.log"
    fi
}

read_dir $1