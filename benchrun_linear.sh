#!/bin/bash

osilbench="$1"
benchname=${osilbench::-5}
timeout="$2"

mkdir -p benchbackups

echo "* Benchmark $benchname"
echo -n "$benchname, " >> allinone.ubs.bstats
echo -n "$benchname, " >> allinone.naive.bstats
echo -n "$benchname, " >> allinone.hybrid.bstats
echo -n "$benchname, " >> onebyone.ubs.bstats
echo -n "$benchname, " >> onebyone.naive.bstats
echo -n "$benchname, " >> onebyone.hybrid.bstats
echo -n "$benchname, " >> nobb.ubs.bstats
echo -n "$benchname, " >> nobb.naive.bstats
echo -n "$benchname, " >> nobb.hybrid.bstats
#echo -n "$benchname, " >> flattened.bstats
echo -n "$benchname, " >> binarized.allinone.ubs.bstats
echo -n "$benchname, " >> binarized.allinone.naive.bstats
echo -n "$benchname, " >> binarized.allinone.hybrid.bstats
echo -n "$benchname, " >> binarized.onebyone.ubs.bstats
echo -n "$benchname, " >> binarized.onebyone.naive.bstats
echo -n "$benchname, " >> binarized.onebyone.hybrid.bstats
echo -n "$benchname, " >> binarized.flattened.ubs.bstats
echo -n "$benchname, " >> binarized.flattened.naive.bstats
echo -n "$benchname, " >> binarized.flattened.hybrid.bstats
echo -n "$benchname, " >> z3opt.bstats
echo "--- ALL-IN-ONE APPROACH / UBS --- "
sense=$(./osil2smt.py --branch-bound $osilbench | grep "* Optimization sense:" |  egrep -o "min|max")
stats=$(eval "(timeout $timeout ./optimize.py -d $sense $benchname.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> allinone.ubs.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> allinone.ubs.bstats
fi
echo "--- ALL-IN-ONE APPROACH / NAIVE --- "
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o naive $benchname.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> allinone.naive.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> allinone.naive.bstats
fi
echo "--- ALL-IN-ONE APPROACH / HYBRID --- "
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o hybrid $benchname.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> allinone.hybrid.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> allinone.hybrid.bstats
fi
echo "--- ONE-BY-ONE APPROACH / UBS ---"
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -i one-by-one $benchname.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> onebyone.ubs.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> onebyone.ubs.bstats
fi
echo "--- ONE-BY-ONE APPROACH / NAIVE ---"
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o naive -i one-by-one $benchname.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> onebyone.naive.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> onebyone.naive.bstats
fi
echo "--- ONE-BY-ONE APPROACH / HYBRID ---"
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o hybrid -i one-by-one $benchname.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> onebyone.hybrid.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> onebyone.hybrid.bstats
fi
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
# echo "--- FLATTENED APPROACH ---"
# stats=$(eval "(timeout $timeout ./optimization.py -b no -i empty.var test.exc.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
# if [[ ! -z  "$stats"  ]]
#   then 
#     echo $stats
#     echo $stats >> flattened.bstats
#   else
#     echo "No solutions found"
#     echo "No solutions found" >> flattened.bstats
# fi
echo "--- BINARIZED NON-FLATTENED ALL-IN-ONE APPROACH / UBS ---"
sense=$(./osil2smt.py --branch-bound $osilbench | grep "* Optimization sense:" |  egrep -o "min|max")
./binarize.py $benchname.smt2 $benchname.smt2.var noflatten
stats=$(eval "(timeout $timeout ./optimize.py -d $sense $benchname.bin.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> binarized.allinone.ubs.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> binarized.allinone.ubs.bstats
fi
echo "--- BINARIZED NON-FLATTENED ALL-IN-ONE APPROACH / NAIVE ---"
./binarize.py $benchname.smt2 $benchname.smt2.var noflatten
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o naive $benchname.bin.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> binarized.allinone.naive.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> binarized.allinone.naive.bstats
fi
echo "--- BINARIZED NON-FLATTENED ALL-IN-ONE APPROACH / HYBRID ---"
./binarize.py $benchname.smt2 $benchname.smt2.var noflatten
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o hybrid $benchname.bin.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> binarized.allinone.hybrid.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> binarized.allinone.hybrid.bstats
fi
echo "--- BINARIZED NON-FLATTENED ONE-BY-ONE APPROACH / UBS ---"
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -i one-by-one $benchname.bin.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> binarized.onebyone.ubs.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> binarized.onebyone.ubs.bstats
fi
echo "--- BINARIZED NON-FLATTENED ONE-BY-ONE APPROACH / NAIVE ---"
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o naive -i one-by-one $benchname.bin.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> binarized.onebyone.naive.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> binarized.onebyone.naive.bstats
fi
echo "--- BINARIZED NON-FLATTENED ONE-BY-ONE APPROACH / HYBRID ---"
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o hybrid -i one-by-one $benchname.bin.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> binarized.onebyone.hybrid.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> binarized.onebyone.hybrid.bstats
fi
echo "--- BINARIZED FLATTENED APPROACH / UBS ---"
./binarize.py $benchname.smt2 $benchname.smt2.var flatten
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -i disabled $benchname.bin.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> binarized.flattened.ubs.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> binarized.flattened.ubs.bstats
fi
echo "--- BINARIZED FLATTENED APPROACH / NAIVE ---"
./binarize.py $benchname.smt2 $benchname.smt2.var flatten
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o naive -i disabled $benchname.bin.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> binarized.flattened.naive.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> binarized.flattened.naive.bstats
fi
echo "--- BINARIZED FLATTENED APPROACH / HYBRID ---"
./binarize.py $benchname.smt2 $benchname.smt2.var flatten
stats=$(eval "(timeout $timeout ./optimize.py -d $sense -o hybrid -i disabled $benchname.bin.smt2 2>/dev/null) | grep -A1 \"STATISTICS\" | tail -n 1")
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo $stats >> binarized.flattened.hybrid.bstats
  else
    echo "No solutions found"
    echo "No solutions found" >> binarized.flattened.hybrid.bstats
fi
echo "--- Z3OPT APPROACH ---"
sense=$(./osil2smt.py $osilbench | grep "* Optimization sense:" |  egrep -o "min|max")
(cat $benchname.smt2 ; echo "" ; echo "(${sense}imize obj)" ; echo "(check-sat)" ; echo "(get-model)" ; echo "") > $benchname.z3opt.smt2
datestart=$(date +"%s.%2N")
stats=$(eval "timeout $timeout /z3opt/bin/z3 $benchname.z3opt.smt2 | egrep -i \"(obj|sat|unsat|unknown|error)\"")
dateend=$(date +"%s.%2N")
duration=$(echo "$datestart $dateend" | awk '{printf "%.2f", $2 - $1}')
if [[ ! -z  "$stats"  ]]
  then 
    echo $stats
    echo -n "$stats " >> z3opt.bstats
  else
    echo "No solutions found"
    echo -n "No solutions found " >> z3opt.bstats
fi
echo "{'Solving time': $duration, 'Total time': $duration}"
echo "{'Solving time': $duration, 'Total time': $duration}" >> z3opt.bstats
basedir="$(basename $benchname)"
mkdir -p "stats/$basedir"
mv *.bstats "stats/$basedir/"

