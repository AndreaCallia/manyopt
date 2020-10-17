from .. import utils

# Constants

increase_factor = 2
initial_diff = 1
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
  verbprint = utils.verbprint
  utils.stats_create("Bisection time", 0.0)
  utils.stats_create("Bisection iterations", 0)
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
  start_up = solver.get_float(feas_model, obj, accuracy)
  verbprint(3, "Initial value for the objective: " + str(start_up), True)
  verbprint(3, "Looking for initial bounds...", True)
  utils.increase_indentation()
  (lower, upper, gbounds_model, naive_found_it) = get_bounds(obj, start_up, accuracy, feas_model)
  utils.decrease_indentation()
  if (naive_found_it == True):
    return gbounds_model
  verbprint(3, "Initial interval: " + str((lower, upper)), True)
  verbprint(3, "Applying bisection...", True)
  utils.increase_indentation()   
  bisec_model = bisection(obj, lower, upper, accuracy, gbounds_model)
  utils.decrease_indentation()
  if (bisec_model != None):
    objval = solver.get_float(bisec_model, obj, accuracy)
    verbprint(3, "Bisection complete. Found objective: " + str(objval), True)
  return bisec_model

def get_bounds(objective, upper, accuracy, feas_model):
  global increase_factor
  global initial_diff
  global solver
  gbounds_model = feas_model
  verbprint = utils.verbprint
  utils.time_start("Bounds search time")
  diff = initial_diff
  push_count = 0
  lower = upper - diff
  iteration = 1
  finished = False
  naive_found_it = False
  while (finished == False):
    verbprint(3, "Iteration " + str(iteration), True)
    verbprint(3, "NAIVE step", True)
    new = upper - accuracy
    verbprint(3, "Trying with value " + str(upper) + " - " + str(accuracy) + " = " + str(new), True)
    verbprint(3, "Adding condition " + str(objective) + " < " + str(new) + " ...", False)
    solver.add_lt(objective, new)
    push_count = push_count + 1
    verbprint(3, "done.", True)
    tmpmodel = solver.check_feasibility()
    verbprint(3, "Result is: " + str("sat" if (tmpmodel != None) else "unsat"), True)
    if (tmpmodel == None):
      finished = True
      naive_found_it = True
    else:
      objval = solver.get_float(tmpmodel, objective, accuracy)
      verbprint(3, "Objective value: " + str(objval), True)
      upper = objval
      gbounds_model = tmpmodel
      verbprint(3, "UBS step", True)
      verbprint(3, "Adding condition " + objective + " < " + str(lower) + " ...", False)
      solver.add_lt(objective, lower)
      push_count = push_count + 1
      verbprint(3, "done.", True)
      tmpmodel = solver.check_feasibility()
      verbprint(3, "Result is: " + str("sat" if (tmpmodel != None) else "unsat"), True)
      if (tmpmodel != None):
        objval = solver.get_float(tmpmodel, objective, accuracy)
        verbprint(3, "Objective (" + objective + ") value: " + str(objval), True)
        upper = objval
        diff = diff * increase_factor
        lower = upper - diff
        verbprint(3, "lower = " + str(lower) + ", upper = " + str(upper), True)
        gbounds_model = tmpmodel
      else:
        verbprint(3, "Removing the last assertion...", False)
        solver.pop(1)
        push_count = push_count - 1
        verbprint(3, "done.", True)
        finished = True
    iteration = iteration + 1
  verbprint(3, "Clearing " + str(push_count) + " initial bounds learned clauses...", False)
  solver.pop(push_count)
  verbprint(3, "done.", True)
  utils.stats_update("Bounds search time", utils.time_take("Bounds search time"))
  utils.stats_update("Bounds search iterations", iteration)
  return lower, upper, gbounds_model, naive_found_it

 
def bisection(objective, lower, upper, accuracy, gbounds_model):
  global solver
  push_count=0
  bisec_model = gbounds_model
  utils.time_start("Bisection time")
  verbprint = utils.verbprint
  iteration=0
  finished = False
  while ((upper - lower > accuracy) and (finished == False)):
    iteration = iteration + 1
    verbprint(3, "Iteration " + str(iteration), True)
    verbprint(3, "NAIVE step", True)
    new = upper - accuracy
    verbprint(3, "Trying with value " + str(upper) + " - " + str(accuracy) + " = " + str(new), True)
    verbprint(3, "Adding condition " + str(objective) + " < " + str(new) + " ...", False)
    solver.add_lt(objective, new)
    push_count = push_count + 1
    verbprint(3, "done.", True)
    tmpmodel = solver.check_feasibility()
    verbprint(3, "Result is: " + str("sat" if (tmpmodel != None) else "unsat"), True)
    if (tmpmodel == None):
      finished = True
    else:
      objval = solver.get_float(tmpmodel, objective, accuracy)
      verbprint(3, "Objective value: " + str(objval), True)
      upper = objval
      bisec_model = tmpmodel
      verbprint(3, "UBS step", True)
      middle = (lower + upper) / 2.0
      verbprint(3, "Trying with lower = " + str(lower) + " and upper = " + str(upper), True)
      verbprint(3, "middle = " + str(middle), True)
      verbprint(3, "Adding condition " + str(objective) + " < " + str(middle) + " ...", False)
      solver.add_lt(objective, middle)
      push_count = push_count + 1
      verbprint(3, "done.", True)
      tmpmodel = solver.check_feasibility()
      verbprint(3, "Result is: " + str("sat" if (tmpmodel != None) else "unsat"), True)
      if (tmpmodel != None):
        objval = solver.get_float(tmpmodel, objective, accuracy)
        verbprint(3, "Objective value: " + str(objval), True)
        upper = min(middle, objval)
        bisec_model = tmpmodel
      else:
        solver.pop(1)
        push_count = push_count - 1
        lower = middle
  verbprint(3, "Clearing " + str(push_count) + " bisection learned clauses...", False)
  solver.pop(push_count)
  verbprint(3, "done.", True)
  utils.stats_update("Bisection time", utils.time_take("Bisection time"))
  utils.stats_update("Bisection iterations", iteration)
  return bisec_model


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


