#!/usr/bin/python

from optstack import intmanagement, croptimization, feasibility, utils

#from optstack.intmanagement import *
#from optstack.croptimization import *
#from optstack.feasibility import *

from sys import stderr
import math
import time
# import ast

from optparse import OptionParser
from argparse import ArgumentParser

#Constants
defaultVerbose = 3
defaultAccuracy = 0.001
defaultObjective = 'obj'
defaultDirection = 'min'
defaultModel = 'model.dat'
defaultIntManager = 'all-in-one'
defaultOptimizer = 'ubsearch'
defaultSolver = 'z3'
noIntFile = False

int_managers = {}
int_managers["all-in-one"] = intmanagement.allinone
int_managers["one-by-one"] = intmanagement.onebyone
int_managers["disabled"] = intmanagement.disabled

optimizers = {}
optimizers["naive"] = croptimization.naive
optimizers["ubsearch"] = croptimization.ubsearch
optimizers["hybrid"] = croptimization.hybrid
optimizers["z3opt"] = croptimization.z3opt

solvers = {}
solvers["z3"] = feasibility.z3
solvers["msat"] = feasibility.pysmt
solvers["cvc4"] = feasibility.pysmt
solvers["yices"] = feasibility.pysmt
solvers["btor"] = feasibility.pysmt
solvers["picosat"] = feasibility.pysmt
solvers["bdd"] = feasibility.pysmt
solvers["smtpipe"] = feasibility.pysmt

pysmtsolvers = ["msat", "cvc4", "yices", "btor", "picosat", "bdd"]

def cmdparse():
  global defaultAccuracy
  global defaultDirection
  global defaultIntManager
  global defaultOptimizer
  global defaultSolver
  global defaultObjective
  global defaultModel
  global defaultVerbose
  global noIntFile
  usage = "Usage: %prog [OPTIONS] FILE\nOpen FILE for optimization."
  optparser = OptionParser(usage)
  optparser.add_option("-a", "--accuracy", dest="accuracy", type="float", default=defaultAccuracy,
                    help="Set ACCURACY as accuracy level for optimization", metavar="ACCURACY")
  optparser.add_option("-d", "--direction", dest="direction", type="choice", default=defaultDirection,
                    help="Set the optimization direction (min or max)", metavar="min|max",
                    choices=['min', 'max'])
  optparser.add_option("-i", "--intmanager", dest="intmanager", type="choice", default=defaultIntManager,
                    help=("Set the integrality manager for integrality constraints.\n"
                      "Available choices are: "
                      "all-in-one (Branch and Bound), "
                      "one-by-one (Branch and Bound), "
                      "or disabled (delegating to the optimization/feasibility layer)."), metavar="all-in-one|one-by-one|disabled",
                    choices=['all-in-one', 'one-by-one', 'disabled'])
  optparser.add_option("-o", "--optimizer", dest="optimizer", type="choice", default=defaultOptimizer,
                    help=("Set the optimizer to solve the continuous relaxation of the problem.\n"
                      "Available choices are: "
                      "naive (Naive method), "
                      "ubsearch (Unbounded Binary Search),"
                      "hybrid (Combination of Naive and UBS), "
                      "z3opt (Z3opt solver from Microsoft (C))."), metavar="naive|ubs|hybrid|disabled",
                      choices=['naive', 'ubsearch', 'hybrid', 'disabled'])
  optparser.add_option("-s", "--solver", dest="solver", type="choice", default=defaultSolver,
                    help=("Set SOLVER as the underlying feasibility solver.\n"
                      "Available choices are: "
                      "z3 (Z3 solver from Microsoft(C)), "
                      "msat (the MathSat solver), "
                      "cvc4 (the CVC4 solver), "
                      "yices (the YICES solver), "
                      "btor (the Boolector solver), " 
                      "picosat (the PicoSAT solver), "
                      "bdd (the CUDD solver), "
                      "smtpipe (any external SMTLIB solver via piping)."), metavar="SOLVER",
                    choices=['z3', 'msat', 'cvc4', 'yices', 'btor', 'picosat', 'bdd', 'smtpipe'])
  optparser.add_option("-p", "--pipe-to", dest="pipe_to", default = None,
                    help="if pipe solving is used, then problems are sent to the program specified by PIPE_SOLVER_PATH via piping.", metavar="PIPE_SOLVER_PATH")
  optparser.add_option("-l", "--pipe-logic", dest="pipe_logic", default = None,
                    help="if pipe solving is used, then the PIPE_LOGIC logic is used, e.g. QF_LRA, QF_NRA, etc. (see the SMTLIB2.0 standard for more examples).", metavar="PIPE_LOGIC")
  optparser.add_option("-O", "--objvar", dest="objective", default=defaultObjective,
                    help="set OBJNAME as the name of the variable assigned to the expression to be optimized", metavar="OBJNAME")
  optparser.add_option("-I", "--intfile", dest="intvarfile", default=None,
                    help="load INTFILE containing a list of all variables which must be integer (default name: INPUTFILE.var)", metavar="INTFILE")
  optparser.add_option("-m", "--modelfile", dest="modelfile",
                    help="save the found model in MODELFILE (default name: INPUTFILE.model)", metavar="MODELFILE")
  optparser.add_option("-S", "--statsfile", dest="statsfile",
                    help="save statistics in STATSFILE (default name: INPUTFILE.stats)", metavar="STATSFILE")
  optparser.add_option("-v", "--verbosity", type="int",
                    dest="verbose", default=defaultVerbose,
                    help="set verbosity level (from 0 to 3)")
  (options, args) = optparser.parse_args()
   
  if len(args) < 1:
    utils.error(utils.CLI_ERROR, "Error: too few arguments.\n")
    
  if len(args) > 1:
    utils.error(utils.CLI_ERROR, "Error: too many arguments.\n")
  
  return options, args


def main():
  global int_managers
  global optimizers
  global solvers
  utils.time_start("Total time")
  final_model = None
  verbprint = utils.verbprint

  #Initialization
  options, args = cmdparse()
  utils.verbosity_level = options.verbose
  objective = options.objective
  optdir = options.direction
  accuracy = options.accuracy
  decdigits = int(-math.log(accuracy, 10)) + 2
  
  #Preparing for optimization
  modelfile = args[0] + ".model" if (options.modelfile == None) else options.modelfile
  statsfile = args[0] + ".stats" if (options.statsfile == None) else options.statsfile
  verbprint(1, "Verbosity level: " + str(options.verbose), True)
  if (options.intmanager in ["all-in-one", "one-by-one"]):
    if (options.intvarfile == None):
      int_filename = args[0] + ".var"
    else:
      int_filename = options.intvarfile
    with open(int_filename) as int_file:
      if (int_file):
        verbprint(2, "Reading integer variables from file " + int_filename + "...", False)
        file_lines = int_file.readlines()
        int_var_data = [eval('({0})'.format(x.strip('\n'))) for x in file_lines]
        intvars = list(x[0] for x in int_var_data)
        verbprint(2, "done.", True)
  else:
    intvars = []
  verbprint(2, "Opening input file " + args[0] + " ...", False)
  with open(args[0], "r") as input_file:
    input_code = input_file.read()
  verbprint(2, "done.", True)
  verbprint(2, "Objective variable: " + objective, True)
  verbprint(2, "Optimization direction: " + optdir, True)
  verbprint(2, "Integrality manager: " + options.intmanager, True)
  verbprint(2, "Continuous relaxation optimizer: " + options.optimizer, True)
  verbprint(2, "Feasibility checker: " + options.solver, True)
  verbprint(2, "Accuracy: " + str(accuracy), True)
  int_manager = int_managers[options.intmanager]
  optimizer = optimizers[options.optimizer]
  solver = solvers[options.solver]
  xoptions = {}
  if (options.solver in pysmtsolvers):
    xoptions["pysmt"] = options.solver
  elif (options.solver == "smtpipe" and options.pipe_to == None):
    verbprint(0, "Error. If 'smtpipe' solver is selected, then options -p or --pipe-to must be used. Use --help for details.", True)
    exit(1)
  elif (options.solver == "smtpipe" and options.pipe_logic == None):
    verbprint(0, "Error. If 'smtpipe' solver is selected, then a logic (e.g. QF_NRA) must be used. Use --help for details.", True)
    exit(1)
  elif (options.solver == "smtpipe"):
    xoptions["smtpipe"] = options.pipe_to
    xoptions["pipe_logic"] = options.pipe_logic
  int_manager.configure(optimizer, solver, xoptions, input_code, optdir)
  final_model, objval = int_manager.solve(intvars, objective, accuracy)
  utils.stats_update("Objective value", objval)
  utils.stats_update("Total time", utils.time_take("Total time"))
  objval = utils.stats["Objective value"]
  if (objval == None):
    verbprint(2, "Optimization complete. No found objectives.", True)
  else:
    verbprint(2, "Optimization complete. Found objective: " + str(utils.stats["Objective value"]), True)
  verbprint(2, "Saving model in file " + modelfile + " ...", False)
  with open(modelfile, "w") as output:
    print >>output, str(final_model)
  verbprint(2, "done.", True)
  verbprint(2, "Saving statistics in file " + statsfile + " ...", False)
  with open(statsfile, "w") as output:
    print >>output, str(utils.stats)
  verbprint(2, "done.", True)
  verbprint(1, "STATISTICS", True)
  verbprint(1, str(utils.stats), True)
  return

main()  
