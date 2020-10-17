from .. import utils

# Constants

neg_obj_name = "neg_obj"

# Attributes

solver = None
negated = False
optdir = 'min'

def configure(solv, options, inpcode, od):
  global solver
  global optdir
  solver = solv
  optdir = od
  solver.configure(inpcode, options)
  
def optimize(objective, accuracy):
  global solver
  global negated
  push_count = 0
  verbprint = utils.verbprint
  utils.time_start("Naive time")
  utils.increase_indentation()
  obj = objective
  if (optdir == 'max'):
    if (negated == False):
      verbprint(3, "Converting maximization problem into minimization problem...", False)
      solver.add_opposite_eq(neg_obj_name, obj)
      negated = True
      verbprint(3, "done.", True)
    obj = neg_obj_name
  feas_model = solver.check_feasibility()
  if (feas_model == None):
    return None
  final_model = feas_model
  first = solver.get_float(feas_model, obj, accuracy)
  verbprint(3, "Initial value for the objective: " + str(first), True)
  iteration=0
  breakloop=False
  current=first
  while (breakloop == False):
    new = current - accuracy
    iteration = iteration + 1
    verbprint(3, "Iteration " + str(iteration), True)
    verbprint(3, "Trying with value " + str(current) + " - " + str(accuracy) + " = " + str(new), True)
    verbprint(3, "Adding condition " + str(obj) + " < " + str(new) + " ...", False)
    solver.add_lt(obj, new)
    push_count = push_count + 1
    verbprint(3, "done.", True)
    tmpmodel = solver.check_feasibility()
    verbprint(3, "Result is: " + str("sat" if (tmpmodel != None) else "unsat"), True)
    if (tmpmodel != None):
      objval = solver.get_float(tmpmodel, obj, accuracy)
      verbprint(3, "Objective value: " + str(objval), True)
      current = objval
      final_model = tmpmodel
    else:
      breakloop = True
  verbprint(3, "done.", True)
  verbprint(3, "Clearing " + str(push_count) + " naive learned clauses...", False)
  solver.pop(push_count)
  verbprint(3, "done.", True)
  utils.stats_update("Naive time", utils.time_take("Naive time"))
  utils.stats_update("Naive iterations", iteration)
  utils.decrease_indentation()
  return final_model

# Auxiliary functions required by above layers

def model_vars(model):
  return solver.model_vars(model)

def is_int(model, x_str):
  return solver.is_int(model, x_str)

def get_model_value(model, x_str):
  return solver.get_model_value(model, x_str)

def get_floor(model, x_str):
  return solver.get_floor(model, x_str)

def get_ceil(model, x_str):
  return solver.get_ceil(model, x_str)
    
def exclude_interval(x, a, b):
  return solver.exclude_interval(x, a, b)

def get_obj(model, objective, accuracy):
  return solver.get_float(model, objective, accuracy)



