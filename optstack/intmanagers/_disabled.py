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
  final_model = optimizer.optimize(objective, accuracy)
  return (final_model, optimizer.get_obj(final_model, objective, accuracy))

