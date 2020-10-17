from .. import utils
from pysmt.shortcuts import Or, Symbol, Solver, And, Real, LE, GE
from pysmt.smtlib.parser import SmtLibParser, get_formula
from pysmt.typing import REAL #, INT
import sys
import math

solver = None

def configure(inpcode):
  global solver
  verbprint = utils.verbprint
  verbprint(2, "Parsing the input...", False)
  parser = SmtLibParser()
  script = parser.get_script(inpcode)
  formula = script.get_last_formula()
  # print "Got a formula: " + str(f)
  verbprint(2, "done.", True)
  verbprint(2, "Initializing the solver...", False)
  solver = Solver(name="msat")
  verbprint(2, "done.", True)
  verbprint(2, "Loading the input file in the solver...", False)
  solver.add_assertion(formula)
  verbprint(2, "done.", True)

def check_feasibility():
  global solver
  verbprint = utils.verbprint
  verbprint(3, "Checking satisfiability...", False)
  utils.time_start("Solving time")
  result = solver.solve()
  utils.stats_update("Solving time", utils.time_take("Solving time"))
  verbprint(3, "done.", True)
  if (result == False):
    return None
  # if (result != sat):
  #  utils.error(utils.UNKNOWN_ERROR, "feasibility: The Z3 solver returned: " + str(result))
  return solver.get_model()

# Auxiliary functions required by aboce layers                                                                         
def pop(n):
  global solver
  for i in range(0, n):
    solver.pop()

def model_vars(model):
  return [str(x) for (x, y) in model]

def is_int(model, x_str):
  x = Symbol(x_str, REAL)
  tmp = (model.get_value(x) - Real(math.floor(float(model.get_value(x))))).simplify().is_zero()
  return tmp

def get_model_value(model, x_str):
  x = Symbol(x_str, REAL)
  return str(model[x])

def get_floor(model, x_str):
  x = Symbol(x_str, REAL)
  flvalue = math.floor(float(model.get_value(x).simplify()))
  return str(flvalue)
  #return str(Real(math.floor(float(model.get_value(x).simplify()))).simplify())
  # return str(simplify(ToInt(model[x])))

def get_ceil(model, x_str):
  x = Symbol(x_str, REAL)
  ceilvalue = math.ceil(float(model.get_value(x).simplify()))
  return str(ceilvalue)
  #return str(float(Real(math.floor(float(model.get_value(x).simplify())).simplify()) + 1))
  # return str(simplify(ToInt(model[x]) + 1))

def exclude_interval(x, a, b):
  global solver
  solver.push()
  var = Symbol(x, REAL)
  solver.add_assertion(Or(LE(var, Real(float(a))), GE(var, Real(float(b)))))

def add_opposite_eq(neg_obj_str, obj_str):
  global solver
  solver.push()
  neg_obj = Symbol(neg_obj_str, REAL)
  obj = Symbol(obj_str, REAL)
  solver.add_assertion(obj + neg_obj == 0)

def get_float(model, x, accuracy):
  val = model.get_py_value(Symbol(x, REAL))
  decdigits = int(-math.log(accuracy, 10)) + 2
  return float(val)

def add_lt(x_str, v):
  global solver
  x = Symbol(x_str, REAL)
  solver.push()
  solver.add_assertion(x < v)

