#!/bin/bash

osilbench="$1"
benchname=${osilbench::-5}
timeout="$2"

mkdir -p benchbackups

echo "* Benchmark $benchname"
echo -n "$benchname, " >> nobb.ubs.bstats
echo -n "$benchname, " >> nobb.naive.bstats
echo -n "$benchname, " >> nobb.hybrid.bstats
#echo -n "$benchname, " >> z3opt.bstats
echo "--- NO BRANCH AND BOUND APPROACH / UBS ---"
sense=$(./osil2smt.py $osilbench | grep "* Optimization sense:" |  egrep -o "min|max")
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -i disabled $benchname.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> nobb.ubs.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> nobb.ubs.bstats
fi
echo "--- NO BRANCH AND BOUND APPROACH / NAIVE ---"
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o naive -i disabled $benchname.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> nobb.naive.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> nobb.naive.bstats
fi
echo "--- NO BRANCH AND BOUND APPROACH / HYBRID ---"
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o hybrid -i disabled $benchname.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> nobb.hybrid.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> nobb.hybrid.bstats
fi
# echo "--- Z3OPT APPROACH ---"
# ./osil2smt.py $osilbench > /dev/null
# (cat $benchname.smt2 ; echo "" ; echo "(${sense}imize obj)" ; echo "(check-sat)" ; echo "(get-model)" ; echo "") > $benchname.z3opt.smt2
# datestart=$(date +"%s.%2N")
# stats=$(eval "timeout $timeout /z3opt/bin/z3 $benchname.z3opt.smt2 | egrep -i \"(obj|sat|unsat|unknown|error)\"")
# dateend=$(date +"%s.%2N")
# duration=$(echo "$datestart $dateend" | awk '{printf "%.2f", $2 - $1}')
# if [[ ! -z  "$stats"  ]]
#   then 
#     echo $stats
#     echo -n "$stats " >> z3opt.bstats
#   else
#     echo "No solutions found"
#     echo -n "No solutions found " >> z3opt.bstats
# fi
# echo "{'Solving time': $duration, 'Total time': $duration}"
# echo "{'Solving time': $duration, 'Total time': $duration}" >> z3opt.bstats
basedir="$(basename $benchname)"
mkdir -p "stats/$basedir"
mv *.bstats "stats/$basedir/"

