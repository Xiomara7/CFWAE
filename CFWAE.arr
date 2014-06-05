#lang pyret/check

#Xiomara Figueroa     801 10 2364
#prof. H. Ortiz       CCOM 4029

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

# Bindings map identifiers to expressions
data Binding:
  | bind (name :: String, value :: CFWAE)
end

#An Environment is a List<Env>
data Env:
  |env (name :: String, value :: CFWAE-Value)
end

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
  | closV (f :: CFWAE, e :: List<Env>) # ExprC must be an fdC
end

fun lookup(s :: String, nv :: List<Env>) -> CFWAE-Value: 
  doc: "lookup search the String s in the environment nv and return it as a CFWAE-Value"
  cases (List) nv:
    | empty => raise("Unbound identifier: " + s)
    | link(enva, r) => 
      arg = enva.name
      if s == enva.name:
        enva.value
      else:
        lookup(s, r)
      end
    end
where:
   lookup("y",[env("x", numV(2))]) raises "Unbound"
   lookup("x",[env("x", numV(2))]) is numV(2)
   lookup("x",[env("x", numV(4)), env("x", numV(3))]) is numV(4)
end
     
fun createStringList(L, keyw) -> List<String>:
  doc: "reads one or more strings and create a list of Strings"
  if not List(L):
    [L]
  else:
    cases (List) L:
      |empty => []
      |link(arg1, rest) =>
       if keyw.member(arg1):
         raise("parse: reserved names cannot be used as identifiers")
       else: 
         key = link(arg1, keyw)
         link(arg1, createStringList(rest, key))
       end
     end
   end
where:
  createStringList(read-sexpr("(x)"), keywords) is ["x"]
  createStringList(read-sexpr("(x y)"), keywords) is ["x", "y"]
  createStringList(read-sexpr("(x y z)"), keywords) is ["x", "y", "z"]
  createStringList(read-sexpr("(x + z)"), keywords) raises("reserved")
  createStringList(read-sexpr("(x x)"), keywords) raises("")
end

fun createBindList(L) -> List<Binding>:
  doc: "reads one or more bonded pairs and create a list of bindings" 
  cases (List) L:
    |empty => []
    |link(arg1, rest)=>
     op = list.index(arg1, 0)
     key = keywords
     if key.member(op):
       raise("parse: reserved names cannot be used as identifiers")
     else:
       key.append([op])
       link(bind(op, parse(list.index(arg1, 1))), createBindList(rest))
     end
  end
  where:
    createBindList([["+", 2]]) raises("reserved")
    createBindList([["x", 2]]) is [bind("x", numC(2))]
    createBindList([["x", 2], ["y", 3]]) is [bind("x", numC(2)), bind("y", numC(3))]      
end

fun createCFWAEList(l) -> List<CFWAE>:
   doc: "reads one or more CFWAE and create a list of CFWAE"
   cases (List) l:
     |empty => []
     |link(ls, rest)=> link(parse(ls), createCFWAEList(rest))
   end
end

operator = ["+", "-", "/", "*"]
keywords = ["+", "-", "/", "*", "fun", "if0", "with"]


fun parse(s) -> CFWAE:
  doc: "Parse reads an s-expression S and returns the abstract syntax tree"
  if Number(s): 
     numC(s)
  else if String(s): 
    if keywords.member(s):
      raise("parse: reserved names cannot be used as identifiers")
    else: 
      idC(s)
    end
  else if List(s):
    cases (List) s:
      | empty => raise("parse: unexpected empty list")
      | link(op, args) => 
          if operator.member(op):
            if args.length() <> 2:
              raise("Parse: need two arguments")
            else:
              argL = list.index(args, 0)
              argR = list.index(args, 1)
              binopC(op, parse(argL), parse(argR)) 
            end
          else if op == "if0": 
            arg1 =  list.index(args, 0)
            arg2 =  list.index(args, 1)
            arg3 =  list.index(args, 2)
            if0C(parse(arg1), parse(arg2), parse(arg3))
          else if op == "fun":
            argL = list.index(args, 0)
            argR = list.index(args, 1)
            fdC(createStringList(argL, keywords), parse(argR))
          else if op == "with":
            last = list.index(args, args.length()-1)
            arg  = args.take(args.length()-1)
            withC(createBindList(arg), parse(last))
          else:
            appC(parse(op), createCFWAEList(args))
          end
        
    end
  end
  
where:
  parse([])raises "empty"
  parse(3) is numC(3)
  parse("+") raises "reserved"
  parse("y") is idC("y")
  parse(["if0", 0, 1, 2]) is if0C(numC(0), numC(1), numC(2))
  parse(["+", 2, 3]) is binopC("+", numC(2), numC(3))
  parse(["-", 7, 2]) is binopC("-", numC(7), numC(2))
  parse(["/", 6, 3]) is binopC("/", numC(6), numC(3))
  parse(["/", 2, 0]) is binopC("/", numC(2), numC(0))
  parse(read-sexpr("(if0 (* 0 1) 1 2)")) is if0C(binopC("*", numC(0), numC(1)), numC(1), numC(2))
  parse(read-sexpr("(if0 (+ 0 1) 3 2)")) is if0C(binopC("+", numC(0), numC(1)), numC(3), numC(2))
  parse(read-sexpr("(if0 (* (+ 4 1) 0) 3 2)")) is if0C(binopC("*", binopC("+", numC(4), numC(1)), numC(0)), numC(3), numC(2))
  parse(read-sexpr("(if0 (- (/ 4 1) 2) 3 2)")) is if0C(binopC("-", binopC("/", numC(4), numC(1)), numC(2)), numC(3), numC(2))
  parse(read-sexpr("(with (x 2)(+ x y))")) is withC([bind("x", numC(2))], binopC("+", idC("x"), idC("y")))
  withC(createBindList([["x", 2]]), parse(["+", "x", "y"])) is withC([bind("x", numC(2))], binopC("+", idC("x"), idC("y")))
  parse(read-sexpr("((fun x (+ x x)) 2)")) is appC(fdC(["x"], binopC("+", idC("x"), idC("x"))), [numC(2)])
  parse(read-sexpr("((fun (x y) (+ x y)) 4 2)")) is appC(fdC(["x", "y"], binopC("+", idC("x"), idC("y"))), [numC(4), numC(2)])
  parse(read-sexpr("(fun (x x) x)")) raises ""
  parse(read-sexpr("(fun x x)")) is fdC(["x"], idC("x"))
end

#Helper functions to interp binopC

fun plus-v(v1, v2): numV(v1.n + v2.n) end
fun mult-v(v1, v2): numV(v1.n * v2.n) end
fun subs-v(v1, v2): numV(v1.n - v2.n) end
fun divs-v(v1, v2): 
  if (v2 == 0):
    raise("Division by zero")     
  else:  
    numV(v1.n / v2.n) 
  end
end

fun bindToEnv(b :: List<Binding>):
  doc: "bindToEnv reads a list of bindings and create an environment"
  cases (List) b:
    |empty => []
    |link(bfirst, r) => val = list.index(bfirst, 1)
                        nv = Env(list.index(bfirst, 0), interp(val))
                        link(nv, bindToEnv(r), mt-env)
  end
end

fun match(v, args, envi):
  cases (List) args:
    | empty => envi
    | link(first, rest)=>
      cases (List) v:
        |empty => envi 
        |link(f, r) => match(r, rest, link(env(f, first), envi))
      end
  end
end

fun interp(e :: CFWAE) -> CFWAE-Value:
  interp_in_env(e, mt-env)
end

fun interp_in_env(e :: CFWAE, nv :: List<Env>) -> CFWAE-Value:
  doc: "Execute the expression E, return the result of evaluation."
  cases (CFWAE) e:
    | numC(n) => numV(n)
    | binopC(op, l, r) =>
      if op == "+":
        plus-v(interp_in_env(l, nv), interp_in_env(r, nv))
      else if op == "*":
        mult-v(interp_in_env(l, nv), interp_in_env(r, nv))
      else if op == "-":
        subs-v(interp_in_env(l, nv), interp_in_env(r, nv))
      else if op == "/":
        divs-v(interp_in_env(l, nv), interp_in_env(r, nv))
      end
    | idC(name) => lookup(name, nv)
    | if0C(test-s, then-s, else-s) => if (interp_in_env(test-s, nv)) == numV(0):
                                          interp_in_env(then-s, nv)
                                      else:
                                        interp_in_env(else-s, nv)
                                      end
    | withC(bs, expr) => new-env = for map(b from bs):
                         env(b.name, interp_in_env(b.value, nv))
                       end
                       new-e = new-env.append(nv)
                       interp_in_env(expr, new-e)
                    
    | fdC(_,_) => closV(e, nv) 
    | appC(f, a) => clos = interp_in_env(f, nv)
                    val = for map(args from a):
                      interp_in_env(args, nv)
                    end
                      interp_in_env(clos.f.body, match(clos.f.args, val, clos.e))
  end
where:
  interp(numC(9)) is numV(9)
  interp(binopC("+", numC(1), numC(3))) is numV(4)
  interp(binopC("-", numC(4), numC(2))) is numV(2)
  interp(binopC("*", numC(3), numC(2))) is numV(6)
  interp(binopC("/", numC(8), numC(2))) is numV(4)
  interp(binopC("/", numC(1), numC(0))) raises ("Division")
  interp(if0C(numC(0), numC(1), numC(2))) is numV(1)
  interp(if0C(numC(1), numC(3), numC(2))) is numV(2)
  interp(if0C(binopC("+", numC(2), numC(3)), numC(0), numC(1))) is numV(1)
  interp(if0C(binopC("*", numC(1), numC(0)), numC(2), numC(1))) is numV(2)
  interp(if0C(binopC("+", binopC("*", numC(2), numC(3)), numC(0)), numC(3), numC(1))) is numV(1)
  interp(if0C(binopC("*", binopC("+", numC(2), numC(3)), numC(0)), numC(0), numC(1))) is numV(0)
  interp(withC([bind("x", numC(2)), bind("y", numC(3))], binopC("+", idC("x"), idC("y")))) is numV(5) 
end

check:
  fun run(s): interp(parse(read-sexpr(s))) end
  run("if0")  raises "reserved"
  run("with") raises "reserved"
  run("fun")  raises "reserved"
  run("-")    raises "reserved"
  run("(if0 1 2 3)") is numV(3)
  run("(if0 0 1 2)") is numV(1)
  run("(+ 3 2)") is numV(5)
  run("(- 4 2)") is numV(2)
  run("(* 3 2)") is numV(6)
  run("(/ 8 2)") is numV(4)
  run("(/ 8 )")  raises ("Parse: need two arguments")
  run("(/ 1 0)") raises ("Division by zero")
  run("(if0 (+ 2 3) 0 1)") is numV(1)
  run("(if0 (* (+ 2 3) 0) 0 1)") is numV(0)  
  run("((fun (x) (+ x x)) 2)") is numV(4)
  run("((fun (self n) (self self n)) (fun (self n) (if0 n 1 (* n (self self (- n 1))))) 5)") is numV(120)
  run("((fun (self n) (self self n)) (fun (self n) (if0 n 0 (+ n (self self (- n 1))))) 10)") is numV(55)  
end
