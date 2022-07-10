#!/bin/bash

function read_dir() {
# echo "" > time.log
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
        echo $file >> filename.log
        
        START_TIME=$[$(date +%s%N)/1000000]
        # python3 avr_pr.py -w workers.txt $file > btorOutput/${file##*\/}.log 
        # timeout 900 ../build/pono -e ic3backbits -k 1000 -v 1 --no-ic3-unsatcore-gen --print-wall-time $file > results/${file##*\/}.log
        timeout 900 ../build/pono -e ic3ia -k 1000 -v 1 --print-wall-time $file > results/${file##*\/}.log
        END_TIME=$[$(date +%s%N)/1000000]
        EXECUTE_TIME=$[$END_TIME-START_TIME]
        
        echo "scale=4;$EXECUTE_TIME/1000" | bc >> time.log
        # echo "btorOutput/${file##*\/}.log"
    fi
}

read_dir $1