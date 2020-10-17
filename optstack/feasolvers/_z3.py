from .. import utils
from z3 import *
import sys
import math

z3solver = None

def configure(inpcode, options):
  global z3solver
  verbprint = utils.verbprint
  verbprint(2, "Parsing the input...", False)
  z3input = z3.parse_smt2_string(inpcode)
  verbprint(2, "done.", True)
  verbprint(2, "Initializing the solver...", False)
  z3solver = z3.Solver()
  # z3solver.set("timeout", 10000)
  verbprint(2, "done.", True)
  verbprint(2, "Loading the input file in the solver...", False)
  z3solver.add(z3input)
  verbprint(2, "done.", True)
  
def check_feasibility():
  global z3solver
  verbprint = utils.verbprint
  utils.stats_create("Solving time", 0.0)
  utils.stats_create("Solver calls", 0)
  verbprint(3, "Checking satisfiability...", False)
  utils.time_start("Solving time")
  result = z3solver.check()
  utils.stats_update("Solving time", utils.time_take("Solving time"))
  utils.stats_update("Solver calls", 1)
  verbprint(3, "done.", True)
  if (result == unsat):
    return None
    # utils.error(UNSAT_ERROR, "feasibility: The problem is unsatisfiable.")
  elif (result == unknown):
    utils.printerror("feasibility: The Z3 solver returned unknown (" + str(z3solver.reason_unknown()) + ")\nUNKNOWN")
    exit(utils.UNKNOWN_ERROR)
  elif (result != sat):
    utils.error(utils.UNKNOWN_ERROR, "feasibility: The Z3 solver returned: " + str(result))
  return z3solver.model()

# Auxiliary functions required by aboce layers

def pop(n):
  global z3solver
  for i in range(0, n):
    z3solver.pop()

def model_vars(model):
  return [str(x) for x in model]

def is_int(model, x_str):
  x = Real(x_str)
  tmp = simplify(model[x] - ToInt(model[x]) == 0)
  return is_true(tmp)

def get_model_value(model, x_str):
  x = Real(x_str)
  return str(model[x])

def get_floor(model, x_str):
  x = Real(x_str)
  return str(simplify(ToInt(model[x])))

def get_ceil(model, x_str):
  x = Real(x_str)
  return str(simplify(ToInt(model[x]) + 1))

def exclude_interval(x, a, b):
  global z3solver
  z3solver.push()
  var = Real(x)
  z3solver.add(Or(var <= a, var >= b))

def add_opposite_eq(neg_obj_str, obj_str):
  global z3solver
  z3solver.push()
  neg_obj = Real(neg_obj_str)
  obj = Real(obj_str)
  z3solver.add(obj + neg_obj == 0)
  
def get_float(model, x, accuracy):
  val = model[Real(x)]
  decdigits = int(-math.log(accuracy, 10)) + 2
  return float(val.as_decimal(decdigits).replace("?", ""))

def add_lt(x_str, v):
  global z3solver
  x = Real(x_str)
  z3solver.push()
  z3solver.add(x < v)
