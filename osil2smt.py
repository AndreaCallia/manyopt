#!/usr/bin/python

import xml.etree.ElementTree as ET
import sys
import os

#Options
pysmt=False
nobranchbound=False

#Utility functions

def URIstrip(name):
    if name[0] == "{":
        uri, tag = name[1:].split("}")
        return tag
    else:
        return name
      
def URIadd(name):
  return "{os.optimizationservices.org}" + name

"""
# Old version
def smt_fmt(f):
  s = str(f)
  n = 0
  if ("e-" in s):
    n = int(s.split("e-", 1)[1])
    if ("." in s):
      n = n + len(s[s.index('.'):s.index('e')]) - 1    
  elif ("." in s):
    n = len(s[s.index('.'):]) -1
  else:
    n = 1
  return "." + str(n) + "f"
"""

"""
def smt_val(f):
  return format(f, smt_fmt(f))
"""

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

#Dictionaries

osil2smt = {}

#Fully supported operators
osil2smt["negate"] = "-"
osil2smt["sum"] = "+"
osil2smt["plus"] = "+"
osil2smt["minus"] = "-"
osil2smt["product"] = "*"
osil2smt["times"] = "*"
osil2smt["divide"] = "/"
osil2smt["power"] = "^"

# Experimental operators: we don't know
# yet whether they work
osil2smt["leq"] = "<="
osil2smt["geq"] = ">="
osil2smt["lt"] = "<"
osil2smt["gt"] = ">"
osil2smt["if"] = "ite"
osil2smt["and"] = "and"
osil2smt["or"] = "or"
experimental = ["leq", "geq", "lt", "gt", "if", "and", "or", "TRUE", "FALSE", "exp"]

#Unsupported operators
unsupported = ["ln", "sin", "cos"]

#Types and optimization keywords
osil2smt["min"] = "minimize"
osil2smt["max"] = "maximize"
osil2smt["C"] = "Real"
osil2smt["D"] = "Real"
osil2smt["I"] = "Int"
osil2smt["B"] = "Int"
osil2smt["S"] = "String"

# index of a variable
index_of = {}

# attributes of a variable
# (name, type, lower bound, upper bound)
# special case for the objective
# (name, min/max)
attrib_of = {}

# index of a constraint
index_of_con = {}

# attributes of a constraint
# (name, lower bound, upper bound, SMTaddends)
# special case for the objective
# (name, SMTaddends)
attrib_of_con = {}

#list of constraint names
con_names = []

# declared variables in the SMT code
smt_declared = []

#Parses the header of the OSiL file
def parse_header(headers):
  for header in headers:
    if header.tag == URIadd("name"):
      print "Osil instance name: " + header.text
      # print >>out, "; parsed osil instance: " + header.text
      # print >>out, ""

#Parses the variables      
def parse_variables(variables):
  global pysmt
  global nobranchbound
  if (variables == None):
    return
  index_count = 0
  for var in variables:
    name = var.attrib["name"] if "name" in var.attrib else ("autogen_var" + str(index_count))
    name = ("autoprefix_var" + name) if name.isdigit() else name
    index_of[name] = index_count
    vtype = "C"
    if "type" in var.attrib:
      vtype = var.attrib["type"]
    else:
      vtype = "C"
    lb = None
    ub = None
    if (vtype == "I"):
      lb = "0.0"
      ub = "100.0"
    if (vtype == "C"):
      lb = "0.0"
    if "lb" in var.attrib:
      lb = float(var.attrib["lb"])
    if "ub" in var.attrib:
      ub = float(var.attrib["ub"])
    if (vtype == "B"):
      if (osil2smt["B"] != "Bool"):
        lb = "0.0"
        ub = "1.0"
      else:
	lb = None
	ub = None
    attrib_of[index_count] = {}
    attrib_of[index_count]["name"] = name
    attrib_of[index_count]["type"] = vtype
    attrib_of[index_count]["lb"] = lb
    attrib_of[index_count]["ub"] = ub
    attrib_of[index_count]["smt_name"] = name
    if (pysmt and (vtype in ["I", "B"]) and nobranchbound):
      attrib_of[index_count]["smt_name"] = "(to_real " + name + ")"
    # print "variable " + name + ", index " + str(index_count) + ", attributes: " + str(attrib_of[index_count])
    # print >>out, "(declare-const " + name + " " + osil2smt[vtype] + ")"
    # print >>out, "(assert (>= "+ name + " " + str(float(attrib_of[index_count]["lb"])) + "))"
    # print >>out, "(assert (<= "+ name + " " + str(float(attrib_of[index_count]["ub"])) + "))"
    # print >>out, ""
    index_count = index_count + 1
 
#Parses the objective
def parse_objectives(objectives):
  if (objectives == None):
    return
  for obj in objectives:
    name = obj.attrib["name"] if "name" in obj.attrib else "autogen_obj"
    name = ("autoprefix_obj" + name) if name.isdigit() else name
    index_of[name] = -1
    attrib_of[-1] = {}
    attrib_of[-1]["name"] = name
    attrib_of[-1]["smt_name"] = name
    attrib_of[-1]["type"] = "C"
    attrib_of[-1]["lb"] = None
    attrib_of[-1]["ub"] = None
    attrib_of[-1]["maxOrMin"] = obj.attrib["maxOrMin"]  
    attrib_of_con[-1] = {}
    attrib_of_con[-1]["name"] = name #"osil2smt_obj"
    attrib_of_con[-1]["lb"] = None
    attrib_of_con[-1]["ub"] = None
    attrib_of_con[-1]["SMTaddends"] = []
    # print "objective " + name + ", direction: " + attrib_of[-1]["maxOrMin"]
    if "constant" in obj.attrib :
      addends = attrib_of_con[-1]["SMTaddends"]
      attrib_of_con[-1]["SMTaddends"] = addends + [smt_val(float(obj.attrib["constant"]))]
    for coef in obj:
      if coef.tag == URIadd("coef"):
	addends = attrib_of_con[-1]["SMTaddends"]
	attrib_of_con[-1]["SMTaddends"] = addends + ["(* " + smt_val(float(coef.text)) + " " + attrib_of[int(coef.attrib["idx"])]["smt_name"] + ")"]
    # print >>out, "(declare-const " + name + " Real)"
    # print >>out, ""

#Parses the objective expression and all the constraints
def parse_constraints(constraints):
  global con_names
  if (constraints == None):
    return
  index_count = 0
  for con in constraints:
    name = con.attrib["name"] if "name" in con.attrib else ("autogen_con" + str(index_count))
    name = ("autoprefix_con" + name) if name.isdigit() else name
    con_names = con_names + [name]
    lb = None
    ub = None
    if "lb" in con.attrib:
      lb = smt_val(float(con.attrib["lb"]))
    if "ub" in con.attrib:
      ub = smt_val(float(con.attrib["ub"]))
    index_of_con[name] = index_count
    attrib_of_con[index_count] = {}
    attrib_of_con[index_count]["name"] = name
    attrib_of_con[index_count]["lb"] = lb
    attrib_of_con[index_count]["ub"] = ub
    attrib_of_con[index_count]["SMTaddends"] = []
    # print "constraint " + name + ", index " + str(index_count) + ", attributes: " + str(attrib_of_con[index_count])
    index_count = index_count + 1

#Populate an array used for the linear constraint coefficient representation
def populate_array(tag, vtype):
  if (tag == None):
    return []
  array = []
  for el in tag:
    if (el.tag == URIadd("el")):
      val = vtype(el.text)
      mult = 1
      incr = 0
      if "mult" in el.attrib:
        mult = int(el.attrib["mult"])
      if "incr" in el.attrib:
        incr = int(el.attrib["incr"])
      for i in range(0, mult):
        array = array + [val]
        val = val + incr
  return array

def parse_by_row(start, rowIdx, value):
  var_count = -1
  start_count = 0
  for i in range(0, len(value)):
    while (start[start_count] == i):
      var_count = var_count + 1
      start_count = start_count + 1
    addends = attrib_of_con[int(rowIdx[i])]["SMTaddends"]
    attrib_of_con[int(rowIdx[i])]["SMTaddends"] = addends + ["(* " + smt_val(value[i]) + " " + attrib_of[var_count]["smt_name"] + ")"]

def parse_by_column(start, colIdx, value):
  eq_count = -1
  start_count = 0
  for i in range(0, len(value)):
    while (start[start_count] == i):
      eq_count = eq_count + 1
      start_count = start_count + 1
    addends = attrib_of_con[eq_count]["SMTaddends"]
    attrib_of_con[eq_count]["SMTaddends"] = addends + ["(* " + smt_val(value[i]) + " " + attrib_of[int(colIdx[i])]["smt_name"] + ")"]

#Parses the linear constraint coefficients
def parse_linear_coefficients(coefficients):
  if (coefficients == None):
    return
  print "* Linear constraint coefficients found."
  start = populate_array(coefficients.find(URIadd("start")), int)
  colIdx = populate_array(coefficients.find(URIadd("colIdx")), int)
  rowIdx = populate_array(coefficients.find(URIadd("rowIdx")), int)
  value = populate_array(coefficients.find(URIadd("value")), float)
  print "colIdx length is: " + str(len(colIdx))
  print "rowIdx length is: " + str(len(rowIdx))
  if (len(rowIdx) > 0 and len(colIdx) > 0):
    print "Error: rowIdx and colIdx are both non-empty. Exiting..."
    exit(1)
  if (len(rowIdx) > 0):
    parse_by_row(start, rowIdx, value)
  else:
    parse_by_column(start, colIdx, value)

#Parses the quadratic coefficients
def parse_quadratic_coefficients(coefficients):
  global pysmt
  if (coefficients == None):
    return
  print "* Quadratic constraint coefficients found."
  for qterm in coefficients:
    if (qterm.tag == URIadd("qTerm")):
      index = int(qterm.attrib["idx"])
      addends = attrib_of_con[index]["SMTaddends"]
      if pysmt:
        attrib_of_con[index]["SMTaddends"] = addends + ["(* " + smt_val(float(qterm.attrib["coef"])) + " (* " + attrib_of[int(qterm.attrib["idxOne"])]["smt_name"] + " " + attrib_of[int(qterm.attrib["idxTwo"])]["smt_name"] + "))"]
      else:
        attrib_of_con[index]["SMTaddends"] = addends + ["(* " + smt_val(float(qterm.attrib["coef"])) + " " + attrib_of[int(qterm.attrib["idxOne"])]["smt_name"] + " " + attrib_of[int(qterm.attrib["idxTwo"])]["smt_name"] + ")"]

warning_printed = []
  
#Converts a non-linear expression into SMT
def smt_nl_conv(exp):
  global warning_printed
  global pysmt
  binary = {URIadd("minus"):'0.0', URIadd("product"):'1.0', URIadd("divide"):'1.0'}
  # print "exp.tag is: " + str(exp.tag)
  #if (URIstrip(exp.tag) in experimental) and not (URIstrip(exp.tag) in warning_printed):
    #print >>sys.stderr, "Warning: the operator " + URIstrip(exp.tag) + " is just experimentally supported. The parser may misbehave."
    #warning_printed = warning_printed + [URIstrip(exp.tag)]
  if URIstrip(exp.tag) in unsupported: #(unsupported + experimental):
    print >>sys.stderr, "Error: the operator " + URIstrip(exp.tag) + " is not supported. Exiting..."
    quit()
  if exp.tag == URIadd("TRUE") :
    return "true"
  if exp.tag == URIadd("FALSE") :
    return "false"
  if exp.tag == URIadd("variable") :
    name = attrib_of[int(exp.attrib["idx"])]["smt_name"]
    if (("coef" in exp.attrib) and (exp.attrib["coef"] != '1')):
      return "(* " + smt_val(float(exp.attrib["coef"])) + " " + name + ")"
    return attrib_of[int(exp.attrib["idx"])]["smt_name"]
  if exp.tag == URIadd("number") :
    return smt_val(float(exp.attrib["value"]))
  if exp.tag == URIadd("power") and pysmt:
    base = smt_nl_conv(exp[0])
    exponent = smt_nl_conv(exp[1])
    if (exponent.endswith(".0")):
      exponent = exponent[0:-2]
    if (not (exponent.isdigit())):
      print >>sys.stderr, "Error: found an exponent which is not an integer constant. This cannot be parsed using the --pysmt option. Exiting..."
      exit(1)
    output = ""
    for i in range(0, int(exponent) - 1):
      output = output + "(* " + base + " "
    output = output + base + ((int(exponent) - 1) * ")")
    return output
  if exp.tag == URIadd("abs") :
    temp = smt_nl_conv(exp[0])
    if pysmt:
      return "(ite (< " + temp + " 0.0) (- 0.0 " + temp + ") " + temp + ")"
    return "(abs " + temp + ")"
  if exp.tag == URIadd("square") :
    temp = smt_nl_conv(exp[0])
    return "(* " + temp + " " + temp + ")" if pysmt else "(^ " + temp + " 2.0)"
  if exp.tag == URIadd("sqrt") :
    temp = smt_nl_conv(exp[0])
    return "(^ " + temp + " 0.5)"
  if exp.tag == URIadd("exp") :
    temp = smt_nl_conv(exp[0])
    return "(^ exp_e " + temp + ")"
  if (pysmt and (exp.tag in binary)):
    output = ""
    operator = osil2smt[URIstrip(exp.tag)]
    for op in exp[0:-1]:
      output = output + "(" + operator + " " + smt_nl_conv(op)
    output = output + " " + smt_nl_conv(exp[-1]) + ((len(exp) - 1) * ")")
    return output
  output = ""
  output = output + "(" + osil2smt[URIstrip(exp.tag)]
  for op in exp:
    output = output + " " + smt_nl_conv(op)
  output = output + ")"
  return output

#Parses the non-linear expressions
def parse_nonlinear_expressions(nlexps):
  if (nlexps == None):
    return
  print "* Non-linear expressions found."
  for nl in nlexps:
    if (nl.tag == URIadd("nl")):  
      index = int(nl.attrib["idx"])
      addends = attrib_of_con[index]["SMTaddends"]
      #if (index == -1):
        #print "Adding the addend: " + str(smt_nl_conv(nl[0]))
      attrib_of_con[index]["SMTaddends"] = addends + [smt_nl_conv(nl[0])]
    # print "non-linear expression: " + smtconv
    # print >>out, "(assert (= obj " + smtconv + "))"
    # print >>out, "(assert (= " + attrib_of[-1]["smt_name"] + " (+ obj 0.1)))"

#Parses the data section of the OSiL file
def parse_data(instance_data):
  # print >>out, "(declare-const obj Real)"
  parse_variables(instance_data.find(URIadd("variables")))
  parse_objectives(instance_data.find(URIadd("objectives")))
  # print "objective addends: " + str(attrib_of_con[-1]["SMTaddends"])
  parse_constraints(instance_data.find(URIadd("constraints")))
  parse_linear_coefficients(instance_data.find(URIadd("linearConstraintCoefficients")))
  parse_quadratic_coefficients(instance_data.find(URIadd("quadraticCoefficients")))
  parse_nonlinear_expressions(instance_data.find(URIadd("nonlinearExpressions")))
  #for i in range(-1, len(attrib_of_con) - 1):
  #  print "The addends of " + attrib_of_con[i]["name"] + " are " + str(attrib_of_con[i]["SMTaddends"])

#Produces the SMT code after parsing OSiL
def make_smt(binflatten):
  global smt_declared
  global con_names
  global pysmt
  # SMT output stored in a string
  smt = ""
  # Declaration of the objective
  smt = smt + "(declare-const obj Real)\n" + ("(assert (= obj obj))\n" if pysmt else "")
  smt = smt + "(declare-const exp_e Real)" + "\n"
  smt = smt + "(assert (= exp_e 2.71828182846))" + "\n\n"
  # Declaration of variables and corresponding bounds
  for i in range(-1, len(attrib_of) - 1):
    if not (attrib_of[i]["name"] in smt_declared):
      smt = smt + "(declare-const " + attrib_of[i]["name"] + " " + osil2smt[attrib_of[i]["type"]] + ")" + "\n"
      if pysmt:
        smt = smt + "(assert (= " + attrib_of[i]["name"] + " " + attrib_of[i]["name"] + "))\n"
      smt_declared = smt_declared + [attrib_of[i]["name"]]
    if (smt_val(attrib_of[i]["lb"]) != None):
      smt = smt + "(assert (>= "+ attrib_of[i]["smt_name"] + " " + smt_val(attrib_of[i]["lb"]) + "))" + "\n"
    if (smt_val(attrib_of[i]["ub"]) != None):
      smt = smt + "(assert (<= "+ attrib_of[i]["smt_name"] + " " + smt_val(attrib_of[i]["ub"]) + "))" + "\n"
    if ((binflatten) and (attrib_of[i]["type"] == "B")):
      smt = smt + "(assert (or (= " + attrib_of[i]["smt_name"] +" 0.0) (= " + attrib_of[i]["smt_name"] + " 1.0)))" + "\n"
    smt = smt + "\n"
  # Representation of constraints and of the objective expression
  for i in range(0, len(attrib_of_con) - 1):
    name = attrib_of_con[i]["name"]
    ub = smt_val(attrib_of_con[i]["ub"])
    lb = smt_val(attrib_of_con[i]["lb"])
    if (i != -1):
     if not (name in smt_declared):
       smt = smt + "(declare-const " + name + " Real)" + "\n"
       if pysmt:
         smt = smt + "(assert (= " + name + " " + name + "))\n"
       smt_declared = smt_declared + [name]
    smt = smt + "(assert (= " + name + " (+ 0.0 "
    for a in attrib_of_con[i]["SMTaddends"]:
      smt = smt + " " + a
    smt = smt + ")))" + "\n"
    if (i == -1):
      smt = smt + "\n"
    elif ((lb == None) and (ub == None)):
      print "Warning: unexpected behaviour, found a constraint with no lower and upper bound. Ignoring..."
    elif (lb == ub):
      smt = smt + "(assert (= " + name + " " + lb + "))" + "\n"
      smt = smt + "\n"
    else:
      if (lb != None):
	smt = smt + "(assert (>= " + name + " " + lb + "))" + "\n"
      if (ub != None):
	smt = smt + "(assert (<= " + name + " " + ub + "))" + "\n"
      smt = smt + "\n"
  # Representation of the objective and its direction (minimization or maximization)
  # if (attrib_of[-1]["maxOrMin"] == "min"):
  smt = smt + "(assert (= obj (+ 0.0 " #  + (attrib_of[-1]["smt_name"] if attrib_of[-1]["smt_name"] in con_names else "")
  print "DOUBLE CHECK"
  for a in attrib_of_con[-1]["SMTaddends"]:
    #print "An addend is: " + a
    smt = smt + " " + a
  smt = smt + ")))" + "\n"
#  elif (attrib_of[-1]["maxOrMin"] == "max"):
#    smt = smt + "(assert (= obj (- ( +" # + (attrib_of[-1]["smt_name"] if attrib_of[-1]["smt_name"] in con_names else "")
#    for a in attrib_of_con[-1]["SMTaddends"]:
#      smt = smt + " " + a
#    smt = smt + "))))" + "\n"
#  else:
#    print "Error: unexpected objective direction (neither 'min' nor 'max'). Exiting..."
#    quit()
  return smt
    # print >>out, "(assert (>= "+ name + " " + str(float(attrib_of[index_count]["lb"])) + "))"
    # print >>out, "(assert (<= "+ name + " " + str(float(attrib_of[index_count]["ub"])) + "))"
    # print >>out, ""

# Makes a list of integer variables in case branch and bound is used.
def make_intlist():
  intvars = ""
  count = 0
  for i in range(0, len(attrib_of) - 1):
    if (attrib_of[i]["type"] in ["I", "B"]):
      if (count > 0):
        intvars = intvars + "\n"
      lb = "0.0"
      ub = "100.0"
      if (attrib_of[i]["type"] == "B"):
        ub = "1.0"
      if (attrib_of[i]["lb"] != None):
        lb = attrib_of[i]["lb"]
      if (attrib_of[i]["ub"] != None):
        ub = attrib_of[i]["ub"]
      intvars = intvars + "\"" + attrib_of[i]["name"] +"\", " + str(lb) + ", " + str(ub)
      count = count + 1
  return intvars

# This is the function which is called to parse OSiL and produce the corresponding SMT code
def parse_osil(data, options):
  if ("--bin2bool" in options):
    osil2smt["B"] = "Bool"
  if ("--branch-bound" in options):
    osil2smt["I"] = "Real"
    osil2smt["B"] = "Real"
  root = ET.fromstring(data)
  parse_header(root.find(URIadd("instanceHeader")))
  parse_data(root.find(URIadd("instanceData")))
  intvars = ""
  if ("--branch-bound" in options):
    intvars = make_intlist()
  return (make_smt(("--bin-flatten" in options)), intvars)

def print_help_message():
  print "                                                                             "
  print "Usage: " + os.path.basename(sys.argv[0]) + " [OPTIONS] OSILFILE              "                                                                                
  print "Converts an OSiL file into an SMT file for SMT-based optimization.           "                                                                                
  print "                                                                             "
  print "It creates an SMT file (.smt2) whose name is based on the OSiL file basename."
  print "                                                                             "                                                                                
  print "Options:                                                                     "                                                                                
  print "  -h, --help            show this help message and exit.                     "                                                                                
  print "  --branch-bound                                                             "                                                                                
  print "                        produce a continuous relaxation of integrality       "
  print "                        constraints in order to apply branch and bound       "
  print "                        approaches. Using this options a special .var file   "
  print "                        containing the list of integer and binary variables  "
  print "                        is also produced.                                    "
  print "  --bin2bool                                                                 "
  print "                        encode the OSiL binary variables as boolean variables"
  print "                        in SMT (by default they are encoded as integer       "
  print "                        variables with 0 as lower bound and 1 as upper       "
  print "                        bound).                                              "
  print "  --bin-flatten                                                              "
  print "                        for each binary variable, using this option a        "
  print "                        special assertion is added to force this variable to "
  print "                        be either 0 and 1. Then branch and bound cannot be   "
  print "                        applied on binary variables.                         "
  print "                                                                             "
  print " --pysmt                                                                     "
  print "                        generates SMT code which is compatible with the      "
  print "                        SMT parser from pySMT.                               "

# Main function
def main():
  global pysmt
  global nobranchbound
  if (("--help" in sys.argv) or ("-h" in sys.argv)):
    print_help_message()
    quit()
  if ("--pysmt" in sys.argv):
    pysmt = True
  if (not ("--branch-bound" in sys.argv)):
    nobranchbound = True
  print "Opening file...",
  data = open(sys.argv[-1]).read()
  args = sys.argv[:-1]
  print "done."
  outfile = sys.argv[-1]
  if outfile.endswith(".xml"):
    outfile = outfile[:-4]
  if outfile.endswith(".osil"):
    outfile = outfile[:-5]
  print "Opening output files...",
  out = open(outfile + ".smt2", "w")
  if ("--branch-bound" in args):
    outvar = open(outfile + ".smt2.var", "w")
  print "done."
  print "Parsing OSiL code..."
  (smt, intvars) = parse_osil(data, args)
  print "...done."
  print "Writing output files...",
  print >>out, smt + "\n"
  out.close()  
  if ("--branch-bound" in args):
    print >>outvar, intvars,
    outvar.close()
  print "done."
  print "DATA ABOUT THE BENCHMARK"
  print "* Number of variables: " + str(len(attrib_of))
  print "* Number of constraints: " + str(len(attrib_of_con))
  print "* Optimization sense: " + attrib_of[-1]["maxOrMin"]

main()
