#!/usr/bin/python

import sys

pysmt = False
flatten = False

def smt_val(f):
  global pysmt
  if (f == None):
    return None
  if (type(f) == str):
    if f.lower() in ["inf", "-inf"]:
      return None
    return f
  s = str(f)
  if s.lower() in ["inf", "-inf"]:
    return None
  if ("e" in s):
    parts = s.split("e", 1)
    base = str(float(parts[0]))
    exp = str(float(parts[1]))
    if pysmt:
      if (exp.endswith(".0")):
        exp = exp[0:-2]
      if (not (exp.isdigit())):
        print >>sys.stderr, "Error: found an exponent which is not an integer constant. This cannot be parsed using the --pysmt option. Exiting..."
        exit(1)
      return "(* " + str(base) + (int(exp) * " (* 10.0") + " 1.0" + int(exp) * ")" + ")"
      # return str(int(base) ** int(exp))
    return "(* " + base + " (^ 10.0 " + exp + ")" + ")"
  return s

def bingenerate(n, l, u):
  global pysmt
  global flatten
  # print "n = " + str(n) + ", l = " + str(l) + ", u = " + str(u),
  conn = "" ; op1 = "" ; op2 = ""
  if flatten == True:
    conn = "or"; op1 = "=" ; op2 = "="
  else:
    conn = "and"; op1 = ">=" ; op2 = "<="
  output = ""
  newvars = ""
  temp = ""
  U = u - l
  # print "and U = " + str(U)
  # print "Maximum size of the value: " + str(U)
  v = int(U) + 1
  i = 0
  p = 1.0
  open_brackets = 0
  if pysmt:
    temp = temp + "(assert (= " + str(n) + " (+ 0.0 (+ " + str(l)
    open_brackets += 1
  else:
    temp = temp + "(assert (= " + str(n) + " (+ 0.0 " + str(l)
  while (v > 0):
    b_i = n + "_b" + str(i)
    newvars = newvars + "\"" + b_i + "\", 0.0, 1.0\n"
    output = output + "(declare-const " + b_i + " Real)\n"
    output = output + "(assert (" + conn + " (" + op1 + " " + b_i + " 0.0) (" + op2 + " " + b_i + " 1.0)))\n"
    if pysmt:
      temp = temp + " (+ (* " + smt_val(p) + " " + b_i + ")"
      open_brackets += 1
    else:
      temp = temp + " (* " + smt_val(p) + " " + b_i + ")"
    v = v / 2
    i = i + 1
    p = p * 2.0
  temp = temp + (open_brackets * ")") + ")))"
  output = output + temp
  return (output, newvars)

def main():
  global pysmt
  global flatten
  output = ""
  newvars = ""
  if ((len(sys.argv) > 5) or (len(sys.argv) < 2)):
    print "Error in parameters (" + str(len(sys.argv)) + "). Exiting."
    exit(2)
  if ("--flatten" in sys.argv):
    flatten = True
  if ("--pysmt" in sys.argv):
    pysmt = True
  filename = ".".join(sys.argv[-1].split(".")[0:-1])
  # varlistfilename = sys.argv[2]
  varlistfilename = filename + ".smt2.var"
  varlist = open(varlistfilename, "r")
  for line in varlist:
    (n, l, u) = eval(line)
    (temp1, temp2) = bingenerate(n, l, u)
    output = output + temp1 + "\n\n"
    newvars = newvars + temp2
  binvars = open(filename + ".bin.smt2.var", "w")
  smtfile = open(sys.argv[-1], "r")
  binasrt = open(filename + ".bin.smt2", "w")
  print >>binvars, newvars,
  for line in smtfile:
    print >>binasrt, line
  print >>binasrt, "\n\n\n\n" + output
  binvars.close()
  smtfile.close()
  binasrt.close()
  #print output

main()
