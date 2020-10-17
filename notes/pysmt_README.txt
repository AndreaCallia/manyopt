Maybe there is a bug in pySMT, since it does not
accept empty responses by Z3 when Z3 is used via
POSIX piping.

There are two possible causes: either it is a bug
in pySMT, or SMTLIB2 does not accept empty
responses and the bug is in Z3 since it would not
follow the SMTLIB2 standard.

In any case, one way to make Z3 work using POSIX
piping is to modify the file solver.py inside
the smtlib folder. An example of path in which
it may be installed is:

/usr/local/lib/python2.7/dist-packages/pysmt/smtlib/solver.py

In order to make the "fix", it is sufficient to
open solver.py and replace the following function:

    def _get_answer(self):
        """Reads a line from STDOUT pipe"""
        res = self.solver_stdout.readline().strip()
        if self.dbg: print("Read: " + str(res))
        return res

with the one below:

    def _get_answer(self):
        """Reads a line from STDOUT pipe"""
        res = "";
        while res == "":
          res = self.solver_stdout.readline().strip()
        if self.dbg: print("Read: " + str(res))
        return res
