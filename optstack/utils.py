import time
import sys
from decimal import Decimal

verbosity_level = 0
found_models = 0
indentation = 0
last_newline = True

#Error handling

CLI_ERROR = 1
IO_ERROR = 2
UNSAT_ERROR = 3
UNKNOWN_ERROR = 4
UNEXPECTED_ERROR = 5

def error(code, message):
  sys.stderr.write(message + "\n")
  exit(code)

#Keeping track of running times

times = {}

def get_time():
  return Decimal("%.2f" % time.time())

def time_start(key):
  global times
  times[key] = get_time()

def time_take(key):
  global times
  end = get_time()
  if not key in times:
    return None
  start = times[key]
  del times[key]
  return str(end - start)

#Statistics

stats = {}

def stats_create(name, val):
  global stats
  if (not (name in stats)):
    stats[name] = val

def stats_update(name, val):
  global stats
  if name in stats:
    stats[name] = str(Decimal(stats[name]) + Decimal(str(val)))
  else:
    stats[name] = str(val)

#Printing

def verbprint(threshold, text, eol):
  global indentation
  global last_newline
  if (verbosity_level >= threshold):
    if (last_newline == True):
      print " " * (indentation - 1),
    if eol:
      print text
      last_newline = True
    else:
      print text,
      last_newline = False

def printerror(text):
  global indentation
  print >>sys.stderr, " " * (indentation - 1),
  print >>sys.stderr, text

def increase_indentation():
  global indentation
  indentation = indentation + 4
  
def decrease_indentation():
  global indentation
  indentation = indentation - 4
  

