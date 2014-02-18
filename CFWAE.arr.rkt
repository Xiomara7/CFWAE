#lang pyret/check

# cfwae.arr - Template of a simple interpreter for CFWAE
# Copyright (C) 2014 - Humberto Ortiz-Zuazaga <humberto.ortiz@upr.edu>

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# Bindings map identifiers to values
data Binding:
  | bind (name :: String, value :: CFWAE-Value)
end

# An Environment is a List<Binding>
mt-env = []
xtnd-env = link

# Data type for expressions
                          
data CFWAE:
  | numC  (n :: Number)
  | binopC(op :: String, l :: CFWAE, r :: CFWAE)
  | withC (bindings :: List<Binding>, expr :: CFWAE)
  | idC   (name :: String)
  | if0C  (test-expr :: CFWAE, then-expr :: CFWAE, else-expr :: CFWAE)
  | fdC   (args :: List<String>, body :: CFWAE)
  | appC  (f :: CFWAE, args :: List<CFWAE>)
end

#and values
       
data CFWAE-Value:
  | numV  (n :: Number)
  | closV (f :: CFWAE, e :: List<Binding>) # ExprC must be an fdC
end

#define lookup
              
     
fun parse(s) -> CFWAE:
  doc: "Parse reads an s-expression S and returns the abstract syntax tree"
  if Number(s): 
     numC(s)
  else if List(s):
    cases (List) s:
      | empty => raise("parse: unexpected empty list")
      | link(op, args) =>
        if args.length() == 1:
          argL = list.index(args, 0)
          if (argL == "+") or (argL == "-")
          or (argL == "/") or (argL == "*")
          or (argL == "with") or (argL == "if0")
          or (argL == "fun"):
            raise("parse: reserved names cannot be used as identifiers")
          else:
            idC(parse(argL))
          end
        else if args.length() == 2:
          argL = list.index(args, 0)
          argR = list.index(args, 1)
          if (op == "+") or (op == "-")
          or (op == "/") or (op == "*"):
            raise("parse: need two arguments to perform arithmetic")
          else:
            raise("pase: ...")
          end
        else if args.length() == 3:
          if op == "if0":
            argIf   =  list.index(args, 0)
            argThen =  list.index(args, 1)
            argElse =  list.index(args, 2)
            if0C(parse(argIf), parse(argThen), parse(argElse))
          else if (op == "+") or (op == "-")
               or (op == "/") or (op == "*"):
               argL =  list.index(args, 1)
               argR =  list.index(args, 2)
               binopC(parse(op), parse(argL), parse(argR))
          else:
            raise("parse: unknown ternary operator")
          end
        end
    end
  else:
    raise("parse: not number or list")
  end
where:
  parse(3) is numC(3)
end

fun plus-v(v1, v2): numV(v1.n + v2.n) end
fun mult-v(v1, v2): numV(v1.n * v2.n) end
fun subs-v(v1, v2): numV(v1.n - v2.n) end
fun divs-v(v1, v2): numV(v1.n / v2.n) end

fun interp(e :: CFWAE) -> CFWAE-Value:
  doc: "Execute the expression E, return the result of evaluation."
  cases (CFWAE) e:
    | numC(n) => numV(n)
    | binopC(op, l, r) =>
      if op == "+":
        plus-v(interp(l), interp(r))
      else if op == "*":
        mult-v(interp(l), interp(r))
      else if op == "-":
        subs-v(interp(l), interp(r))
      else if op == "/":
        if r == 0:
          raise("interp: cannot divide by zero") 
        else:
          divs-v(interp(l), interp(r))
        end
      end
    | idC(name) => raise("parse error")  
    | if0C(test-s, then-s, else-s) => if (interp(test-s) <> 0):
                                        interp(then-s)
                                      else:
                                        interp(else-s)
                                      end
    | withC => 0
    | fdC(_,_) => closV(e, xtnd-env) 
    | appC(f, a) => 
      clos = interp(f, xtnd-env)
      arg-val = interp(a, xtnd-env)
      interp(clos.f.body, xtnd-env(bind(clos.f.arg, arg-val), clos.e))
  end
where:
  interp(if0C(numC(0), numC(1), numC(2))) is numV(2)
  interp(if0C(numC(1), numC(3), numC(2))) is numV(3)
end

check:
  fun run(s): interp(parse(read-sexpr(s))) end
  run("(if0 0 1 2)") is numV(2)
  run("(if0 1 2 3)") is numV(2)
end
