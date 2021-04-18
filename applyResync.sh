#!/bin/bash

if [ -d reordered_proj ]; then
	rm -rf reordered_proj
fi
cp -r $1 reordered_proj

inputDir=$1
dbDir=$2

# dbDir needs to be empty to be used as a database target
if [ -d $dbDir ]; then
	echo "Using existing QL database (rm -r the database dir if you want to rebuild)"
else
	# this script assumes codeql is properly set up 
	# build the database for the specified project
	codeql database create --language=javascript --source-root $inputDir $dbDir
	codeql database upgrade $dbDir
fi


# # now, get the pairs to reorder
codeql query run --database=$dbDir --output=temp_swaps.bqrs --ram=25600 console_getStmtAndSets.ql
codeql bqrs decode --format=csv temp_swaps.bqrs | tail -n+2 > swaps.csv # remove the header
rm temp_swaps.bqrs

# get all the statements in all the files where reordering will happen
# this is going to be the input to the parse tree
# this python call generates the QL query we use
python3 fake_external_data_getAllStmts.py nocalls # the nocalls argument means we're not also timing a list of function calls (an old test metric)
codeql query run --database=$dbDir --output=temp_allStmts.bqrs getAllStmts_codeql.ql  
codeql bqrs decode --format=csv temp_allStmts.bqrs | tail -n+2 > allStmts.csv # remove the header
rm temp_allStmts.bqrs

# now, apply the reordering to the project
# the paths need to be absolute here
python3 reorder_me.py `readlink -f $inputDir` `readlink -f reordered_proj` > /dev/null 2>&1