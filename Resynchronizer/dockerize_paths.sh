#!/bin/bash
  
sed -i s!/home/ellen/Documents/ASJProj/TESTING_reordering/!/home/resynchronizer/!g $1/test_list.txt
sed -i s!python!python3!g $1/batchListOfTests.sh 