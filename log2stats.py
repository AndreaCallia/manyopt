#!/usr/bin/python

import sys
#import matplotlib.pyplot as plt
import matplotlib
matplotlib.use("Agg")
import pylab as plt
import errno    
import os
from matplotlib.ticker import FuncFormatter


def mkdir_p(path):
    try:
        os.makedirs(path)
    except OSError as exc:  # Python >2.5
        if exc.errno == errno.EEXIST and os.path.isdir(path):
            pass
        else:
            raise

def tlen(tl):
  count = 0
  for t in tl:
    if (t == True):
      count += 1
  return count

def dumpunsolved(statlist):
  statfile = open("stats/unsolved.stat", "w")
  for s in statlist:
    print >> statfile, s
  statfile.close()

def dumpstats(statlist):
  statfile = open("stats/stats.stat", "w")
  for s in statlist:
    print >> statfile, s
  statfile.close()
  
def dumpunsolvdict(statdict):
  statfile = open("stats/unsolved.dict", "w")
  print >> statfile, statdict
  statfile.close()

def dumpsolvdict(statdict):
  statfile = open("stats/solved.dict", "w")
  print >> statfile, statdict
  statfile.close()

def csvstats(statlist):
  csvfile = open("stats/stats.csv", "w")
  print >> csvfile, "Benchmark,Category,Size,Vars,Cons,Found objective,Solved by,Solver calls,Solving time,Total time"
  for s in statlist:
    print >> csvfile, s["Benchmark"] + "," + s["Category"] + "," + s["Size"] + "," + s["Variables"] + "," + s["Constraints"] + "," + s["Objective value"] + "," + s["Solved by"] + "," + s["Solver calls"] + "," + s["Solving time"] + "," + s["Total time"]
  csvfile.close()
  
def latexstats(statlist):
  latexfile = open("stats/stats.tex", "w")
  print >> latexfile, "\\documentclass[a4paper,landscape]{article}"
  print >> latexfile, "\\usepackage[margin=2cm]{geometry}"
  #print >> latexfile, "\\usepackage{geometry}"
  print >> latexfile, "\\usepackage{calc}"
  print >> latexfile, "\\newcommand*{\\thead}[1]{\\multicolumn{1}{|c|}{\\bfseries \\begin{tabular}{c} #1 \\end{tabular}}}"
  #print >> latexfile, "\\newcommand*{\\thead}[1]{\\multicolumn{1}{|c|}{\\bfseries #1}}"
  print >> latexfile, "\\newlength{\\negspace}"
  print >> latexfile, "\\setlength{\\negspace}{0pt-\\widthof{ }}"
  print >> latexfile, "\\begin{document}"
  print >> latexfile, "\\begin{center}"
  print >> latexfile, "\\textbf{\\large{Statistics for solved benchmarks}}\\\\[0.5\\baselineskip]"
  print >> latexfile, "\\begin{tabular}{|l|l|r|r|r|r|r|r|r|} \\hline"
  print >> latexfile, "\\thead{Benchmark} & \\thead{Category} & \\thead{\\#Var} & \\thead{\\#Con} & \\thead{Found \\\\ objective} & \\thead{Solved by} & \\thead{Solver \\\\ calls} & \\thead{Solving \\\\ time} & \\thead{Total \\\\ time}\\\\ \\hline "
  print >> latexfile, "\\rule{0pt}{3ex}\\hspace{\\negspace}"
  # statlist = 1000 * statlist Just for testing it with big lists
  for i in range(0, len(statlist)):
    if ((i + 1) % 36 == 0):
      print >> latexfile, "\\hline  \\end{tabular}"
      print >> latexfile, "\\end{center}"
      print >> latexfile, "\\newpage"
      print >> latexfile, "\\begin{center}"
      print >> latexfile, "\\begin{tabular}{|l|l|r|r|r|r|r|r|r|} \\hline"
      print >> latexfile, "\\thead{Benchmark} & \\thead{Category} & \\thead{\\#Var} & \\thead{\\#Con} & \\thead{Found \\\\ objective} & \\thead{Solved by} & \\thead{Solver \\\\ calls} & \\thead{Solving \\\\ time} & \\thead{Total \\\\ time}\\\\ \\hline "
      print >> latexfile, "\\rule{0pt}{3ex}\\hspace{\\negspace}"
    print >> latexfile,statlist[i]["Benchmark"].replace("_", "\\_") + " & " +statlist[i]["Category"] + " & " +statlist[i]["Variables"] + " & " +statlist[i]["Constraints"] + " & "  +statlist[i]["Objective value"] + " & " +statlist[i]["Solved by"].replace("_", "\\_") + " & " +statlist[i]["Solver calls"] + " & " +statlist[i]["Solving time"] + " & " +statlist[i]["Total time"] + " \\\\"
  print >> latexfile, "\\hline"
  print >> latexfile, "\\end{tabular}"
  print >> latexfile, "\\end{center}"
  print >> latexfile, "\\end{document}"
  latexfile.close()

def percent(y, pos):
  s = "%.0f" % (100 * y)
  return s + "%"
    
def makeplot(statlist, unsolved):
  times = range(0, 1801)
  solved_in_time = []
  plt.yticks([(n/10.0) for n in range(0,11)])
  # plt.yticks(range(0, len(statlist) + len(unsolved) + 1))
  for t in times:
    s = tlen(x <= t for x in (eval(s["Total time"]) for s in statlist))
    solved_in_time += [float(s) / (len(statlist) + len(unsolved)) ]
  #print "Points:"
  #for i in range(0,31):
  #  print "(" + str(times[i]) + ", " + str(solved_in_time[i]) + ")"  
  plt.plot(times, solved_in_time, 'b', marker='', linestyle='-', label='f')
  #plt.axis([0, 1800, 0, len(statlist) + len(unsolved)])
  plt.axis([0, 1800, 0, 1])
  formatter = FuncFormatter(percent)
  plt.gca().yaxis.set_major_formatter(formatter)
  plt.xlabel('time')
  plt.ylabel('solved benchmarks')
  #plt.show()
  plt.savefig('stats/stats.png')

def filterlist(l, cat):
  return list(filter(lambda d: d["Category"] in cat, l))

mkdir_p("stats")

categoriesL = ['LP', 'BLP', 'MBLP', 'ILP', 'MILP']
categoriesQ = ['QP', 'BQP', 'MBQP', 'IQP', 'MIQP']
categoriesQC = ['QCP', 'BQCP', 'MBQCP', 'IQCP', 'MIQCP']
categoriesQCQ = ['QCQP', 'BQCQP', 'MBQCQP', 'IQCQP', 'MIQCQP']
categoriesNL = ['NLP', 'BNLP', 'MBNLP', 'INLP', 'MINLP']
categories = categoriesL + categoriesQ + categoriesQC + categoriesQCQ + categoriesNL

allQP = ['QP', 'QCP', 'QCQP']
allMBQP = ['BQP', 'MBQP', 'BQCP', 'MBQCP', 'BQCQP', 'MBQCQP']
allMIQP = ['IQP', 'MIQP', 'IQCP', 'MIQCP', 'IQCQP', 'MIQCQP']

allNLP = ['LP', 'QP', 'QCP', 'QCQP', 'NLP']
allMBNLP = ['BLP', 'MBLP', 'BQP', 'MBQP', 'BQCP', 'MBQCP', 'BQCQP', 'MBQCQP', 'BNLP', 'MBNLP']
allMINLP = ['ILP', 'MILP', 'IQP', 'MIQP', 'IQCP', 'MIQCP', 'IQCQP', 'MIQCQP', 'INLP', 'MINLP']

errormessages = []
errormessages += ["No methods have found a solution within the timeout."]
errormessages += ["Errors found, for some feature vectors the SMT solver returned UNKNOWN."]
errormessages += ["All features vectors reported an error."]
errormessages += ["For all feature vectors the SMT solver returned UNKNOWN."]

errmsg2errcode = {}
errmsg2errcode[errormessages[0]] = "TIMEOUT"
errmsg2errcode[errormessages[1]] = "ERROR_UNKNOWN"
errmsg2errcode[errormessages[2]] = "ERROR"
errmsg2errcode[errormessages[3]] = "UNKNOWN"

byname = False

if (sys.argv[1] == "--sort"):
  byname = True
  sys.argv = [sys.argv[0]] + sys.argv[2:]

f = open(sys.argv[1], "r")
filtercat = categories
if (len(sys.argv) == 3):
  filtercat = eval(sys.argv[2])
lines = f.readlines()
looking_for_details = False
looking_for_solver = False
looking_for_stats = False
benchname = ""
category = ""
size = ""
nvars = ""
ncons = ""
solvername = ""
solvdict = {}
unsolvdict = {}
solvedlist = []
unsolvedlist = []
i = 0
while (i < len(lines)):
  if lines[i].startswith("* Benchmark "):
    benchname = lines[i].split("* Benchmark ")[1].strip()
    if (len(benchname) < 1):
      print >> sys.stderr, "ERROR in line " + str(i + 1) + ": empty benchmark name"
      exit(1)
    folders = lines[i + 1].strip().split("Path: ")[1].split("/")
    if (tlen(d in categories for d in folders) > 1):
      print >> sys.stderr, "ERROR in line " + str(i + 1) + ": multiple categories?"
      exit(1)
    for d in folders:
      if (d in categories):
	category = d
    if (category == ""):
      category = "--"
    size = lines[i + 2].split("Size: ")[1].strip()
    i = i + 3
    looking_for_details = True
  elif lines[i].startswith("Problem details"):
    if (not looking_for_details):
      print >> sys.stderr, "ERROR: Malformed input in line " + str(i + 1) + ": not looking for details"
      exit(1)
    nvars = lines[i + 1].split("Number of variables: ")[1].strip()
    ncons = lines[i + 2].split("Number of constraints: ")[1].strip()
    i = i + 3
    looking_for_solver = True
    looking_for_details = False
  elif lines[i].startswith("Solution found by: "):
    if (not looking_for_solver):
      print >> sys.stderr, "ERROR: Malformed input in line " + str(i + 1) + ": not looking for solver"
      exit(1)
    solvername = lines[i].split("Solution found by: ")[1].strip()
    looking_for_stats = True
    looking_for_solver = False
    i = i + 1
  elif (lines[i].strip() in errormessages):
    if (not looking_for_solver):
      print >> sys.stderr, "ERROR: Malformed input in line " + str(i + 1) + ": not looking for solver"
      exit(1)
    stats = {}
    stats["Benchmark"] = benchname.split("/")[-1]
    stats["Category"] = category
    stats["Size"] = size
    stats["Variables"] = nvars
    stats["Constraints"] = ncons
    stats["Unsolved because"] = errmsg2errcode[lines[i].strip()]
    unsolvdict[stats["Benchmark"]] = stats
    unsolvedlist += [stats]
    looking_for_solver = False
    benchmark = ""
    category = ""
    size = ""
    i = i + 1
  elif lines[i].strip().startswith("STATISTICS"):
    if (not looking_for_stats):
      print >> sys.stderr, "ERROR: Malformed input in line " + str(i + 1) + ": not looking for stats"
      exit(1)
    stats = eval(lines[i + 1])
    if (not ("Total time" in stats)):
      print >> sys.stderr, "ERROR: total time expected in the line below (line " + str(i + 2) + "):"
      print >> sys.stderr, lines[i + 1]
      exit(1)
    stats["Benchmark"] = benchname.split("/")[-1]
    stats["Category"] = category
    stats["Size"] = size
    stats["Variables"] = nvars
    stats["Constraints"] = ncons
    stats["Solved by"] = solvername
    solvdict[stats["Benchmark"]] = stats
    solvedlist += [stats]
    looking_for_stats = False
    benchmark = ""
    category = ""
    size = ""
    nvars = ""
    ncons = ""
    solvername = ""
    i = i + 2
  elif lines[i].strip().startswith("{"):
    print >> sys.stderr, "ERROR: unexpected brackets in line " + str(i + 1) + ". The line is below:"
    print >> sys.stderr, lines[i]
    exit(1)
  else:
    i = i + 1
if (byname):
  unsolvedlist = [unsolvdict[k] for k in sorted(unsolvdict)]
  solvedlist = [solvdict[k] for k in sorted(solvdict)]
f_unsolvedlist = filterlist(unsolvedlist, filtercat)
f_solvedlist = filterlist(solvedlist, filtercat)
f_unsolvdict = {}
f_solvdict = {}
for b in f_unsolvedlist:
  if b["Category"] in filtercat:
    f_unsolvdict[b["Benchmark"]] = b
for b in f_solvedlist:
  if b["Category"] in filtercat:
    f_solvdict[b["Benchmark"]] = b
if (len(f_unsolvdict) > 0): dumpunsolvdict(f_unsolvdict)
if (len(f_solvdict) > 0): dumpsolvdict(f_solvdict)
if (len(unsolvedlist) > 0): dumpunsolved(f_unsolvedlist)
if (len(solvedlist) > 0): dumpstats(f_solvedlist)
if (len(solvedlist) > 0): csvstats(f_solvedlist)
if (len(solvedlist) > 0): latexstats(f_solvedlist)
if (len(solvedlist) > 0 and len(unsolvedlist) > 0): makeplot(f_solvedlist, f_unsolvedlist)
print >> sys.stderr, "Solved: " + str(len(f_solvedlist)) + " out of " + str(len(f_solvedlist) + len(f_unsolvedlist))
print >> sys.stderr, "Percentage: %2.2f" % (100.0 * float(len(f_solvedlist)) / (len(f_solvedlist) + len(f_unsolvedlist))) + "%"
f.close()

