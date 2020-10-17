from .. import utils

optimizer = None
optdir = 'min'

def configure(opt, solv, options, inpcode, od):
  global optimizer
  global optdir
  optimizer = opt
  optdir = od
  optimizer.configure(solv, options, inpcode, od)
  
def solve(intvars, objective, accuracy):
  global optimizer
  global optdir
  final_model = None
  verbprint = utils.verbprint
  iteration = 0
  mustcontinue = True
  utils.increase_indentation()
  while (mustcontinue == True):
    iteration = iteration + 1
    mustcontinue = False
    verbprint(3, "Branch and bound iteration: " + str(iteration), True)
    tmpmodel = optimizer.optimize(objective, accuracy)  
    if (tmpmodel == None):
      verbprint(3, "No models can satisfy the required integrality constraints.", True)  
    else:
      first_one=True
      for x in optimizer.model_vars(tmpmodel):
        if x in intvars:
	  xval = optimizer.get_model_value(tmpmodel, x)
	  if (optimizer.is_int(tmpmodel, x) and (first_one == True)):
            verbprint(3, "The value " + xval + " for variable " + x + " is integer as requested. Nothing to do here.", True)
          else:
            mustcontinue = True
	    if (first_one==True):
	      first_one = False
	      a = optimizer.get_floor(tmpmodel, x)
	      b = optimizer.get_ceil(tmpmodel, x)
              verbprint(3, "The value " + xval + " for variable " + x + " is not integer.", True)
              verbprint(3, "Adding condition: " + x + " <= " + a + " OR " + x + " >= " + b + " ...", False)
              optimizer.exclude_interval(x, a, b)
              verbprint(3, "done.", True)
      if (mustcontinue == False):
	final_model = tmpmodel
  utils.stats_update("Branch and bound iterations", iteration)
  utils.decrease_indentation()
  if (final_model == None):
    return (None, None)
  return (final_model, optimizer.get_obj(final_model, objective, accuracy))
  
