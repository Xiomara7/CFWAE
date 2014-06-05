#lang pyret/check

# cfwaepp-template.arr - Template of a interpreter for CFWAE++
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

# Data type for expressions
data FieldP:
  | fieldP (name :: String, value :: ExprP)
end

data ExprP:
  | ObjectP (fields :: List<FieldP>)

  | FuncP (args :: List<String>, body :: ExprP)
  | AppP (func :: ExprP, args :: List<ExprP>)
  | DefvarP (id :: String, bind :: ExprP, body :: ExprP)
  | DeffunP (name :: String, ids :: List<String>, funbody :: ExprP, body :: ExprP)
  | IdP (name :: String)

  | GetfieldP (o :: ExprP, field :: ExprP)
  | SetfieldP (o :: ExprP, field :: ExprP, newval :: ExprP)
  | SetvarP (id :: String, val :: ExprP)

  | WhileP (test :: ExprP, body :: ExprP)
  | ForP (init :: ExprP, test :: ExprP, update :: ExprP, body :: ExprP)

  | SeqP (es :: List<ExprP>)
  | IfP (cond :: ExprP, thn :: ExprP, els :: ExprP)

  | NumP (n :: Number)
  | StrP (s :: String)
  | TrueP
  | FalseP

# An op is one of '+ '- '== 'print '< '>
  | PrimP (op :: String, args :: List<ExprP>)
end                          

data FieldC:
  | fieldC (name :: String, value :: ExprC)
end

data ExprC:

  | ObjectC (fields :: List<FieldC>)
  | GetFieldC (obj :: ExprC, field :: ExprC)
  | SetFieldC (obj :: ExprC, field :: ExprC, value :: ExprC)

  | FuncC (args :: List<String>, body :: ExprC)
  | AppC (func :: ExprC, args :: List<ExprC>)
  | LetC (id :: String, bind :: ExprC, body :: ExprC)
  | IdC (id :: String)
  | SetC (id :: String, value :: ExprC)

  | IfC (cond :: ExprC, thn :: ExprC, els :: ExprC)
  | SeqC (e1 :: ExprC, e2 :: ExprC)

  | NumC (n :: Number)
  | StrC (s :: String)
  | TrueC
  | FalseC

  | ErrorC (expr :: ExprC)

# The core operations are 'String+ 'num+ 'num- '== '< '> 'print 'tagof
  | Prim1C (op :: String, arg :: ExprC)
  | Prim2C (op :: String, arg1 :: ExprC, arg2 :: ExprC)
end

# Environments and Values
data Binding:
  | bind (name :: String, value :: Number)
end

# Environments are lists of bindings
mt-env = []
xtnd-env = link


# Helper function to generate stateful counters for store
fun mk-counter(): 
  var ctr = 0
  fun ():
    ctr := ctr + 1
    ctr
  end
end

new-loc = mk-counter()

data FieldV:
  | fieldV (name :: String, value :: ValueC)
end

data ValueC:
  | TrueV
  | FalseV
  | NumV (n :: Number)
  | StrV (s :: String)
  | ClosureV (args :: List<String>, body :: ExprC, env :: List<Binding>)
  | ObjectV (fields :: List<FieldV>)
end

fun pretty-value(v :: ValueC) -> String:
  cases (ValueC) v:
    | ObjectV(_) => "object"
    | ClosureV(_, _, _) => "function"
    | NumV(n) => torepr(n)
    | StrV(n) => n
    | TrueV => "true"
    | FalseV => "false"
  end
end

# helper function for errors
interp-error = raise

# The store maps locations to values
data Cell:
  | cell (location :: Number, value :: ValueC)
end

# The store is a list of cells
mt-sto = []
xtnd-sto = link

data Result:
  | v-x-s (value :: ValueC, store :: List<Cell>)
end

binops = ["+", "-", "==", "<", ">"]
keywords = ['if', 'fun', 'true', 'false', 'defvar', 'deffun', 'obj', 'getfield', 'setfield', 'setvar', 'begin', 'while', 'print', 'for']

fun parse-formals(s, illegals) -> List<String>:
  doc: "Read a list of identifiers S and construct a list of Strings"
  if List(s):
    cases (List) s:
      | empty => empty
      | link(first, rest) =>
        if illegals.member(first):
          raise("parse-formals: formal arguments must be named uniquely")
        else:
          link(first, parse-formals(rest, link(first, illegals)))
        end
    end
  else:
    raise("parse-formals: illegal formal arguments")
  end
where:
  parse-formals(["x", "y"], keywords) is ["x", "y"]
end

fun parse-fields(lof) -> List<FieldP>:
  for map(field from lof):
    name = field.first
    val = parse(list.index(field, 1))
    fieldP(name, val)
  end
end

fun parse(s) -> ExprP:
  doc: "Parse reads an s-expression S and returns the abstract syntax tree."
  if Number(s):
    # num
    NumP(s)
  else if String(s):
    # true
    if s == "true":
      TrueP
    # false
    else if s == "false":
      FalseP
    # id
    else:
      IdP(s)
    end
  else if List(s):
    cases (List) s:
      | empty => raise("parse: empty sexpr")
      | link(op, r) =>
        len = r.length()
        # while
        if "while" == op:
          if len == 2:
            t = parse(list.index(r, 0))
            b = parse(list.index(r, 1))
            WhileP(t, b)
          else:
            raise("parse: malformed while" + s)
          end
        # string
        else if "string" == op:
          if len == 1:
            StrP(r.first)
          else:
            raise("parse: malformed string" + r)
          end
        # + - == < >
        else if binops.member(op):
          if len == 2:
            PrimP(op, [parse(list.index(r, 0)), parse(list.index(r, 1))])
          else:
            raise("parse: binary operations require two arguments")
          end
        # print
        else if "print" == op:
          if len == 1:
            PrimP(op, [parse(r.first)])
          else:
            raise("parse: print requires a single argument")
          end
        # if
        else if "if" == op:
          if len == 3:
            cond = parse(list.index(r, 0))
            then = parse(list.index(r, 1))
            esle = parse(list.index(r, 2))
            IfP(cond, then, esle)
          else:
            raise("parse: malformed if expression")
          end
        # begin
        else if "begin" == op:
          es = for map(e from r):
            parse(e)
          end
          SeqP(es)
        # defvar
        else if "defvar" == op:
          if len == 3:
            id = list.index(r, 0)
            val = parse(list.index(r, 1))
            bod = parse(list.index(r, 2))
            DefvarP(id, val, bod)
          else:
            raise("parse: malformed defvar")
          end
        # setvar
        else if "setvar" == op:
          if len == 2:
            id = list.index(r, 0)
            val = parse(list.index(r, 1))
            SetvarP(id, val)
          else:
            raise("parse: malformed setvar")
          end
        # for
        else if "for" == op:
          if len == 4:
            args = for map(arg from r):
              parse(arg)
            end
            init = list.index(args, 0)
            test = list.index(args, 1)
            update = list.index(args,2)
            body = list.index(args, 3)
            ForP(init, test, update, body)
          else:
            raise("parse: malformed for " + torepr(s))
          end
          # fun
        else if "fun" == op:
          if len == 2:
            formals = parse-formals(list.index(r, 0), keywords)
            body = parse(list.index(r, 1))
            FuncP(formals, body)
          else:
            raise("parse: malformed function definition")
          end
          # obj
        else if "obj" == op:
          if len == 1:
            ObjectP(parse-fields(r.first))
          else:
            raise("parse: malformed object" + torepr(s))
          end
          # getfield
        else if "getfield" == op:
          if len == 2:
            obj = parse(list.index(r, 0))
            field = parse(list.index(r, 1))
            GetfieldP(obj, field)
          else:
            raise("parse: malformed getfield" + torepr(s))
          end
          # setfield
        else if "setfield" == op:
          if len == 3:
            obj = parse(list.index(r, 0))
            field = parse(list.index(r, 1))
            val = parse(list.index(r, 2))
            SetfieldP(obj, field, val)
          else:
            raise("parse: malformed setfield" + torepr(s))
          end
          # deffun
        else if "deffun" == op:
          if len == 3:
            ids = list.index(r, 0)
            funbody = parse(list.index(r, 1))
            body = parse(list.index(r, 2))
            DeffunP(ids.first, ids.rest, funbody, body)
          else:
            raise("parse: malformed fun " + torepr(s))
          end
        else:
          # app
          AppP(parse(s.first), map(parse, s.rest))
        end
    end
  else:
    raise("parse: unknown expression " + torepr(s))
  end
where:
  fun p(s): parse(read-sexpr(s)) end 
  p("3") is NumP(3)
  p("(while true 5)") is WhileP(TrueP, NumP(5))
  p("(for (setvar x 0) (< x 10) (setvar x (+ x 1)) 
    (print x))") is ForP(SetvarP("x", NumP(0)), PrimP("<", [IdP("x"), NumP(10)]), SetvarP("x", PrimP("+", [IdP("x"), NumP(1)])), PrimP("print", [IdP("x")]))
  # NOTE: strings must be enclosed in double quotes
  # You can put them inside single quotes, or escape them
  p("\"hello\"") is StrP("hello")
  p('"hello"') is StrP("hello")
  p("(print (+ 2 3))") is PrimP("print", [PrimP("+", [NumP(2), NumP(3)])])
  p("(if true 1 2)") is IfP(TrueP, NumP(1), NumP(2))
  p("(begin 1 2 3)") is SeqP([NumP(1), NumP(2), NumP(3)])
  p("(defvar x 1 x)") is DefvarP('x', NumP(1), IdP('x'))
  p("(setvar x 2)") is SetvarP('x', NumP(2))
  p("(for 0 true 1 2)") is ForP(NumP(0), TrueP, NumP(1), NumP(2))
  p("(fun (x) x)") is FuncP(['x'], IdP("x"))
  p("(obj ((x 1) (f (fun (x) x))))") is ObjectP([fieldP("x", NumP(1)), fieldP("f", FuncP(['x'], IdP("x")))])
  p('(getfield o "x")') is GetfieldP(IdP('o'), StrP('x'))
  p('(setfield o "x" 2)') is SetfieldP(IdP('o'), StrP('x'), NumP(2))
  p("(deffun (id x) x 3)") is DeffunP("id", ["x"], IdP('x'), NumP(3)) 
  p("(deffun (id x) x (id 3))") is DeffunP("id", ["x"], IdP('x'), AppP(IdP("id"), [NumP(3)])) 
end

# Humberto's desugar
fun desugar-fields(fields :: List<FieldP>) -> List<FieldC>:
  for map(field from fields):
    name = field.name
    val = desugar(field.value)
    fieldC(name, val)
  end
end

fun desugar-begin(es :: List<ExprP>) -> ExprC:
  len = es.length()
  if len == 0:
    ErrorC(StrC("empty sequence of expressions"))
  else if len == 1:
    desugar(es.first)
  else if len == 2:
    SeqC(desugar(list.index(es, 0)), desugar(list.index(es, 1)))
  else:
    SeqC(desugar(es.first), desugar-begin(es.rest))
  end
end

fun desugar(e :: ExprP) -> ExprC:
  doc: "Desugar the expression E, return the equivalent in the core language."
  cases (ExprP) e:
    | TrueP => TrueC
    | FalseP => FalseC
    | NumP(n) => NumC(n)
    | StrP(s) => StrC(s)
    | IdP(name) => IdC(name)
    | IfP(tst, thn, els) => IfC(desugar(tst), desugar(thn), desugar(els))
    | FuncP(formals, body) => FuncC(formals, desugar(body))
    | AppP(func, actuals) => AppC(desugar(func), map(desugar, actuals))
    | ObjectP(fields) => ObjectC(desugar-fields(fields))
    | GetfieldP(o, f) => GetFieldC(desugar(o), desugar(f))
    | SetfieldP(o, f, v) => SetFieldC(desugar(o), desugar(f), desugar(v))
    | DefvarP(id, val, body) => LetC(id, desugar(val), desugar(body))
    | SetvarP(id, val) => SetC(id, desugar(val))
    | DeffunP(n, ids, fb, b) =>
      dummy-fun = FuncC([], ErrorC(StrC("Dummy function")))
      LetC(n, dummy-fun,
        SeqC(SetC(n, FuncC(ids, desugar(fb))),
          desugar(b)))
    | SeqP(es) => desugar-begin(es)
    | WhileP(test, body) =>
      dummy-fun = FuncC([], ErrorC(StrC("Dummy function")))
      IfC( desugar(test),
       # while-var will hold the actual function once we tie
       # everything together
       LetC( "while-var", dummy-fun,
         LetC( "while-func", 
           # this function does the real work - it runs the body of
           # the while loop, then re-runs it if the test is true, and
           # stops if its false
            FuncC([],
              LetC("temp-var",
                desugar( body),
               IfC(desugar( test),
                  AppC(IdC( "while-var"), []),
                  IdC( "temp-var")))),
           # The SetC here makes sure that 'while-var will resolve
           # to the right value later, and the AppC kicks things off
           SeqC(SetC( "while-var", IdC( "while-func")),
              AppC(IdC("while-var"), [])))),
       FalseC)
    | ForP(init, test, update, body) =>
      dummy-fun = FuncC([], ErrorC(StrC("Dummy function")))
      LetC("for-init", desugar(init),
        IfC(desugar(test),
          # set up recursion
          LetC("for-var", dummy-fun,
            LetC("for-fun",
              FuncC([], 
                LetC("for-body", desugar(body),
                  LetC("for-update", desugar(update),
                    LetC("for-test", desugar(test),
                      IfC(IdC("for-test"),
                        AppC(IdC("for-var"), []),
                        IdC("for-body")))))),
              SeqC(
                SetC("for-var", IdC("for-fun")),
                AppC(IdC("for-var"), [])))),
          IdC("for-init")))
    | PrimP(op, args) =>
      len = args.length()
      if 1 == len:
        Prim1C('print', desugar(args.first))
      else if 2 == len:
        argL = desugar(list.index(args, 0))
        argR = desugar(list.index(args, 1))
        if op == '+':
        LetC("tag-l", Prim1C('tagof', argL),
          LetC("tag-r", Prim1C('tagof', argR),
            IfC(Prim2C("==", IdC("tag-l"), IdC("tag-r")),
              IfC(Prim2C("==", IdC("tag-l"), StrC("string")),
                  Prim2C("string+", argL, argR),
                  Prim2C("num+", argL, argR)),
                ErrorC(StrC("Bad arguments to +")))))
        else if op == '-':
          Prim2C("num-", argL, argR)
        else:
          Prim2C(op, argL, argR)
        end
      else:
        ErrorC(StrC("Bad primop"))
      end
  end
where:
  fun run(s): desugar(parse(read-sexpr(s))) end
  run("true") is TrueC
  run("false") is FalseC
  run("0") is NumC(0)
  run('"Hello, World!"') is StrC("Hello, World!")
  run("x") is IdC("x")
  run("(fun (x) x)") is FuncC(["x"], IdC("x"))
  run("((fun (x) x) 5)") is AppC(FuncC(["x"], IdC("x")), [NumC(5)])
  run("(if true 1 0)") is IfC(TrueC, NumC(1), NumC(0))
  run("(obj ((x 5)))") is ObjectC([fieldC("x", NumC(5))])
  run('(getfield (obj ((x 5))) "x")') is GetFieldC(ObjectC([fieldC("x", NumC(5))]), StrC("x"))
  run("(setvar x 2)") is SetC("x", NumC(2))
  run("(deffun (id x) x (id 3))") is
  LetC("id",  FuncC([], ErrorC(StrC("Dummy function"))),
    SeqC(SetC("id", FuncC(["x"], IdC("x"))),
      AppC(IdC("id"), [NumC(3)]) ))
  run("(begin 1 2)") is SeqC(NumC(1), NumC(2))
  run("(begin 1 2 3)") is SeqC(NumC(1), SeqC(NumC(2), NumC(3)))
  run("(while true 1)") is IfC(TrueC, LetC("while-var", FuncC([], ErrorC(StrC("Dummy function"))), LetC("while-func", FuncC([], LetC("temp-var", NumC(1), IfC(TrueC, AppC(IdC("while-var"), []), IdC("temp-var")))), SeqC(SetC("while-var", IdC("while-func")), AppC(IdC("while-var"), [])))), FalseC)
  run("(defvar x 0 (for (setvar x 0) (< x 10) (setvar x (+ x 1)) 
  (print x)))") is LetC("x", NumC(0), LetC("for-init", SetC("x", NumC(0)), IfC(Prim2C("<", IdC("x"), NumC(10)), LetC("for-var", FuncC([], ErrorC(StrC("Dummy function"))), LetC("for-fun", FuncC([], LetC("for-body", Prim1C("print", IdC("x")), LetC("for-update", SetC("x", LetC("tag-l", Prim1C("tagof", IdC("x")), LetC("tag-r", Prim1C("tagof", NumC(1)), IfC(Prim2C("==", IdC("tag-l"), IdC("tag-r")), IfC(Prim2C("==", IdC("tag-l"), StrC("string")), Prim2C("string+", IdC("x"), NumC(1)), Prim2C("num+", IdC("x"), NumC(1))), ErrorC(StrC("Bad arguments to +")))))), LetC("for-test", Prim2C("<", IdC("x"), NumC(10)), IfC(IdC("for-test"), AppC(IdC("for-var"), []), IdC("for-body")))))), SeqC(SetC("for-var", IdC("for-fun")), AppC(IdC("for-var"), [])))), IdC("for-init"))))
  run("(for a b c d)") is LetC("for-init", IdC("a"), IfC(IdC("b"), LetC("for-var", FuncC([], ErrorC(StrC("Dummy function"))), LetC("for-fun", FuncC([], LetC("for-body", IdC("d"), LetC("for-update", IdC("c"), LetC("for-test", IdC("b"), IfC(IdC("for-test"), AppC(IdC("for-var"), []), IdC("for-body")))))), SeqC(SetC("for-var", IdC("for-fun")), AppC(IdC("for-var"), [])))), IdC("for-init")))
  # The primops
  desugar(PrimP("<", [IdP("x"), NumP(10)])) is Prim2C("<", IdC("x"), NumC(10))
end

fun lookup(s :: String, nv :: List<Binding>) -> Number: 
  cases (List<Binding>) nv:
    | empty => raise("unbound identifier: " + s)
    | link(f, r) =>
        if s == f.name:
          f.value
        else:
          lookup(s, r)
        end
   end
where: 
   lookup("y",[bind("x", 2)]) raises "unbound identifier: "
   lookup("x",[bind("x", 2)]) is 2
   lookup("x",[bind("x", 4), bind("x", 3)]) is 4
end

fun fetch(n :: Number, st :: List<Cell>) -> ValueC: 
  cases (List<Cell>) st:
    | empty => raise("unbound identifier: " + n)
    | link(f, r) =>
        if n == f.location:
          f.value
        else:
          fetch(n, r)
        end
   end
where: 
   fetch(4, [cell(2, NumV(2))]) raises "unbound identifier: "
   fetch(2, [cell(2, NumV(2))]) is NumV(2)
   fetch(4, [cell(4, NumV(4)), cell(3, NumV(3))]) is NumV(4)
end

fun Apply(val, args, clos-args, clos-e, clos-s):
  if (is-ClosureV(val)):       
    e-list = eval-exprs(args, clos-e, clos-s)
    if (clos-args.length() == e-list.length()):
      l = new-loc()
      if (clos-args.length() == 1):
        b-v  = interp-full(val.body, xtnd-env(bind(clos-args.first, l), clos-e), xtnd-sto(cell(l, e-list.first), clos-s))
        v-x-s(b-v.value, b-v.store)
      else if (clos-args.length() > 1):
        Apply(val, args.rest, clos-args.rest, xtnd-env(bind(clos-args.first, l), clos-e), xtnd-sto(cell(l, e-list.first), clos-s))
      else:
         b-v  = interp-full(val, xtnd-env(bind(clos-args.first, l), clos-e), xtnd-sto(cell(l, e-list.first), clos-s))
         v-x-s(b-v.value, b-v.store)
      end
    else:
      interp-error("Application failed with arity mismatch")
    end
  else:
    interp-error("Not a function: ")
  end
end

fun eval-exprs(exp :: List<ExprC>, env, st):
  eval-exprs-helper(exp, env, st, [[]])
end

fun eval-exprs-helper(exp :: List<ExprC>, env, st, final-exprs):
  cases (List<ExprC>) exp:
    | empty => final-exprs.rest
    | link(e, rest) => 
           e-v = interp-full(e, env, st)
           final-e = final-exprs.append([e-v.value])
           eval-exprs-helper(rest, env, e-v.store, final-e)
  end
end

fun eval-args(args :: List, env, st):
  doc: "call the helper function to evaluate args"
  print(args)
  eval-args-helper(args, env, st, [[]])
end

fun eval-args-helper(args :: List, env, st, final-args):
  doc: "Helper function to evaluate args"
  cases (List) args:
    | empty => final-args.rest
    | link(f, rest) => f-v = interp-full(f, env, st)
                       final-a = final-args.append([f-v.value])
                       eval-args-helper(rest, env, f-v.store, final-a)
  end
end

fun eval-fields(fields :: List<FieldC>, env, st):
  doc: "call the helper function to evaluate fields"
  eval-fields-helper(fields, env, st, [[]])
end

fun eval-fields-helper(fields :: List<FieldC>, env, st, final-fields):
  doc: "Helper function to evaluate fields and return them with the most recent store"
  cases (List<FieldC>) fields:
    | empty => v-x-s(ObjectV(final-fields.rest), st)
    | link(f, rest) => f-v = interp-full(f.value, env, st)
                       names = f.name
                       value = f-v.value
                       final-f = final-fields.append([fieldV(names, value)])
                       eval-fields-helper(rest, env, f-v.store, final-f)
  end
end

fun helper-subt (a1 :: ValueC, a2 :: ValueC, st): 
  doc: "Helper function to perform the subtraction"
  cases (ValueC) a1:
    | NumV(n1) => 
        cases (ValueC) a2:
          | NumV(n2) => 
              v-x-s(NumV(a1.n - a2.n), st) 
          | else => 
              interp-error("Bad arguments to -")
        end
    | else => interp-error("Bad arguments to -")
  end
where: 
  helper-subt(NumV(9),   NumV(2), []) is v-x-s(NumV(7), [])
  helper-subt(NumV(5),   NumV(2), []) is v-x-s(NumV(3), [])
  helper-subt(StrV("a"), NumV(2), []) raises "Bad arguments to -"
end

fun helper-equal(a1 :: ValueC, a2 :: ValueC, st): 
  doc: "Helper function to perform the equality comparison"
  if (a1.n == a2.n):
    v-x-s(TrueV, st)
  else:
    v-x-s(FalseV, st)
  end
where:
  helper-equal(NumV(9), NumV(9), []) is v-x-s(TrueV,  [])
  helper-equal(NumV(9), NumV(3), []) is v-x-s(FalseV, [])
end

fun helper-plus (a1 :: ValueC, a2 :: ValueC, st): 
  doc: "Helper function to perform the addition"
  if (ValueC(a1) and ValueC(a2)):
    cases (ValueC) a1:
      | NumV(n1) => cases (ValueC) a2:
                     | NumV(n2) => v-x-s(NumV(a1.n + a2.n), st)
                     | StrV(s)  => interp-error("Bad arguments to +")
                   end
      | StrV(s1) => cases (ValueC) a2:
                     | NumV(n)  => interp-error("Bad arguments to +")
                     | StrV(s2) => v-x-s(StrV(a1.s.append(a2.s)), st)
                   end
    end
    else: 
      interp-error("Bad arguments to +")
    end
where:
  helper-plus(NumV(9), NumV(9), []) is v-x-s(NumV(18), [])
  helper-plus(NumV(9), StrV("a"), []) raises "Bad arguments to +"
  helper-plus(StrV("ho"), StrV("la"), []) is v-x-s(StrV("hola"), [])

end

fun helper-compare(op, a1 :: ValueC, a2 :: ValueC, st):
  doc: "Helper function to compare [less than and greater than]"
  cases (ValueC) a1:
    | NumV(n1) => 
        cases (ValueC) a2:
          | NumV(n2) => if (op == "<"):
              if (a1.n < a2.n): 
                  v-x-s(TrueV,  st)
              else: v-x-s(FalseV, st)
              end
              else if (op == ">"):
              if (a1.n > a2.n): 
                  v-x-s(TrueV,  st)
              else: v-x-s(FalseV, st)
              end
              else: 
                interp-error("Bad arguments to compare")
              end            
          | else => 
                interp-error("Bad arguments to compare")
        end
      | else => interp-error("Bad arguments to compare")
  end
where:
  helper-compare("<", NumV(9),  NumV(8), []) is v-x-s(FalseV, [])
  helper-compare("<", NumV(7),  NumV(8), []) is v-x-s(TrueV,  [])
  helper-compare(">", NumV(7),  NumV(8), []) is v-x-s(FalseV, [])
  helper-compare(">", NumV(9),  NumV(8), []) is v-x-s(TrueV,  [])
  helper-compare(">", StrV("a"),NumV(8), []) raises "Bad arguments to compare"
end

fun get-fields(fields, name):
  doc: "function to get the value in the field"
  cases (List<FieldV>) fields:
    | empty => interp-error("unbound identifier")
    | link(f, r) => 
        if (name == f.name):
            f.value
        else:
            get-fields(r, name)
        end
  end
where: 
  get-fields([fieldV("x", NumV(2))], "x") is NumV(2)
  get-fields([fieldV("x", NumV(2)), fieldV("y", NumV(8))], "x") is NumV(2)
  get-fields([fieldV("x", NumV(2)), fieldV("y", NumV(8))], "y") is NumV(8)
  get-fields([fieldV("y", NumV(4))], "x") raises "unbound identifier"

end

fun set-fields(fields, name):
  doc: "function to set the value in the field"
  cases (List<FieldV>) fields:
    | empty => interp-error("unbound identifier")
    | link(f, r) => 
        if (name == f.name):
            f.value
        else:
            set-fields(r, name)
        end
  end
end

# Templates for interpreter: fix interp-full

fun interp-full (expr :: ExprC, env :: List<Binding>, store :: List<Cell>) -> Result:
  doc: "Execute the expression ExprC, return the result of evaluation [ValueC, store]."
  cases (ExprC) expr:
    | NumC (n) => v-x-s(NumV(n), store)
    | StrC (s) => v-x-s(StrV(s), store)
    | IdC (id) => v-x-s(fetch(lookup(id, env), store), store)
    | ErrorC(e)=> v-x-s(interp(e), store) 

    | TrueC  => v-x-s(TrueV ,  store)
    | FalseC => v-x-s(FalseV,  store)

    | SeqC (e1, e2) => seq-e1 = interp-full(e1, env, store)
                       seq-e2 = interp-full(e2, env, seq-e1.store)
                       v-x-s(seq-e2.value, seq-e2.store)
    | ObjectC (fields)  => eval-fields(fields, env, store) 
    | Prim1C (op, arg)  => if (op == "print"):
                             a = interp-full(arg, env, store)
                             v-x-s(a.value, store) 
                           else if (op == "tagof"):
                             a = interp-full(arg, env, store)
                             print(a)
                             if (is-NumV(a.value)): 
                               v-x-s(a.value, a.store)
                             else if (is-StrV(a.value)):  
                               v-x-s(a.value, a.store)
                             else: 
                               interp-error("Error en tagof")
                             end
                           else: 
                             interp-error("Undefined operator")
                           end
    | FuncC(args, body) => v-x-s(ClosureV(args, body, env), store)
    | AppC (func, args) => clos = interp-full(func, env, store)
                           value = clos.value
                           Apply(value, args, clos.value.args, clos.value.env, clos.store)
                                                                                        
    | SetC (id, value)  =>  val = interp-full(value, env, store)
                            loc = lookup(id, env)
                            new-sto = xtnd-sto(cell(loc, val.value), val.store)
                            v-x-s(val.value, new-sto)

    | LetC (id, b, body)=> loc = new-loc()
                           interp-b = interp-full(b, env, store)
                           nv = xtnd-env(bind(id, loc), env)
                           ns = xtnd-sto(cell(loc, interp-b.value), interp-b.store)
                           body-val = interp-full(body, nv, ns)
                           v-x-s(body-val.value, body-val.store)
                             
                            
    | GetFieldC (obj, field) => obj-v = interp-full(obj, env, store)
                                fld-v = interp-full(obj, env, obj-v.store)
                                f = obj-v.value.fields
                                v-x-s(get-fields(f, field.s), fld-v.store)

    | Prim2C (op, arg1, arg2)=> a1-val = interp-full(arg1, env, store)
                                a2-val = interp-full(arg2, env, a1-val.store)  
                                if (op == "+"):
                                  helper-plus(a1-val.value, a2-val.value, a2-val.store)
                                else if (op == "-"): 
                                  helper-subt(a1-val.value, a2-val.value, a2-val.store)
                                else if (op == "=="):
                                  helper-equal(a1-val.value, a2-val.value, a2-val.store)
                                else if (op == "<"):
                                  helper-compare(op, a1-val.value, a2-val.value, a2-val.store)
                                else if (op == ">"): 
                                  helper-compare(op, a1-val.value, a2-val.value, a2-val.store)
                                end
    | SetFieldC (obj, field, value) => obj-v = interp-full(obj, env, store)
                                       fld-v = interp-full(value, env, obj-v.store)
                                       f-v = fieldV(field.s, fld-v.value)
                                       f = obj-v.value.fields.append([f-v])
                                       v-x-s(ObjectV(f), fld-v.store) 

    | IfC (cond, thn, els)   => if-cond = interp-full(cond, env, store)
                                if (if-cond.value == TrueV):
                                  interp-full(thn, env, if-cond.store)
                                else: 
                                  interp-full(els, env, if-cond.store)
                                end
    | else => interp-error("Haven't covered a case yet:".append(torepr(expr)))
  end
where:
  interp(NumC(5)) is NumV(5)
  interp(StrC("Xio")) is StrV("Xio")
  interp(ErrorC(StrC("Error"))) is StrV("Error")
  interp(SeqC(NumC(1), NumC(2))) is NumV(2)
  interp(Prim1C("print", NumC(4))) is NumV(4)
  interp(IfC(TrueC,   NumC(1), NumC(0)))  is NumV(1)
  interp(Prim2C("+",  NumC(2), NumC(10))) is NumV(12)
  interp(Prim2C("==", NumC(2), NumC(2)))  is TrueV
  interp(Prim2C("==", NumC(4), NumC(6)))  is FalseV
  interp(Prim2C("-",  NumC(7), NumC(3)))  is NumV(4)
  interp(Prim2C("<",  NumC(5), NumC(3)))  is FalseV
  interp(Prim2C("<",  NumC(1), NumC(3)))  is TrueV
  interp(Prim2C(">",  NumC(5), NumC(3)))  is TrueV
  interp(Prim2C(">",  NumC(1), NumC(3)))  is FalseV
  interp(Prim2C(">",  NumC(1), StrC("a"))) raises "Bad arguments to compare"
  interp(Prim2C("+",  NumC(2), StrC("a"))) raises "Bad arguments to +"
  interp(Prim2C("-",  StrC("a"), NumC(2))) raises "Bad arguments to -"
  interp(Prim2C("+",  StrC("Xio"), StrC("mara"))) is StrV("Xiomara")
  interp(GetFieldC(ObjectC([fieldC("x", NumC(5))]), StrC("x"))) is NumV(5)
  interp(SetFieldC(ObjectC([fieldC("x", NumC(5))]), StrC("y"), NumC(9))) is ObjectV([fieldV("x", NumV(5)), fieldV("y", NumV(9))])
  interp(SeqC(NumC(2), StrC("Hello"))) is StrV("Hello") 
  interp(ObjectC([fieldC("x", NumC(5)), fieldC("y", NumC(7))])) is ObjectV([fieldV("x", NumV(5)), fieldV("y", NumV(7))])
  interp(FuncC(["x"], NumC(3))) is ClosureV(["x"], NumC(3), [])
  interp(AppC(FuncC(["x"], IdC("x")), [NumC(5)])) is NumV(5) 
  interp(AppC(FuncC(["x", "y"], IdC("y")), [NumC(5), NumC(3)]))is NumV(3) 
  interp(LetC("x", NumC(5), Prim2C("+",  IdC("x"), IdC("x")))) is NumV(10)
  interp(LetC("x", NumC(5), Prim2C("-",  IdC("x"), IdC("x")))) is NumV(0)
  interp(LetC("x", NumC(5), Prim2C("==", IdC("x"), IdC("x")))) is TrueV
  interp(LetC("x", NumC(9), SetC("x", NumC(3))))

end


fun interp(expr :: ExprC) -> ValueC:
  cases (Result) interp-full(expr, mt-env, mt-sto):
    | v-x-s (value, store) => value
  end
end

check:
  fun run(e): interp(desugar(parse(read-sexpr(e)))) end
  run("((fun (x) x) 1)") is NumV(1)
  run("true") is TrueV
  run("false") is FalseV
  run("0") is NumV(0)
  run('"Hello, World!"') is StrV("Hello, World!")
  run('"x"') is StrV("x")
  run("(fun (x) x)") is ClosureV(["x"], IdC("x"), [])
  run("((fun (x) x) 5)") is NumV(5)
  run("(if true 1 0)") is NumV(1)
  run("(obj ((x 5)))") is ObjectV([fieldV("x", NumV(5))])
  run('(getfield (obj ((x 5))) "x")') is NumV(5)
  run("(begin 1 2)") is NumV(2)
  run("(begin 1 2 3)") is NumV(3) 
# Humberto's tests from piazza
  run("((fun (x) x) 1)") is NumV(1)
  run("(defvar x 3 ((fun (y) (+ x y)) 2))") is NumV(5)
  run("(defvar x 3 ((fun (y) (+ x y)) (begin (setvar x 1) 2)))") is NumV(3)
  # My **exhaustive** test cases
  run("5") is NumV(5)
  run("\"unestring\"") is StrV("unestring")
  run("true") is TrueV
  run("false") is FalseV
  run("(== 5 5)") is TrueV
  run("(== 5 4)") is FalseV
  run("(== 5 \"unestring\")") is FalseV
  run("(== \"5\" 5)") is FalseV
  run("(== \"5\" \"5\")") is TrueV
  run("(defvar x 5 (== 5 x))") is TrueV
  run("(== true true)") is TrueV
  run("(== false false)") is TrueV
  run("(== true false)") is FalseV
  run("(== false true)") is FalseV
  run("(== (fun (y) (+ x y)) (fun (y) (+ x y)))") is TrueV
  run("(== (obj ((x 5))) (obj ((x 5))))") is TrueV
  run("(== (obj ((x 5))) (obj ( (x 5) (y 4) )))") is FalseV
  run("(== (obj ((x 5))) (obj ((x 4))))") is FalseV
  run("(> 5 4)") is TrueV
  run("(< 5 4)") is FalseV
  run("(> 5 true)") raises "Bad arguments for >: 5 true"
  run("(defvar x 0 (for (setvar x 0) (< x 10) (setvar x (+ x 1)) 
  (print x)))") is StrV("9")
end

check:
  interp(NumC(5)) is NumV(5)
  interp(TrueC) is TrueV
  interp(FalseC) is FalseV
  interp(StrC("un estring")) is StrV("un estring")
  interp(IfC(TrueC, NumC(5), NumC(6))) is NumV(5)
  interp(IfC(FalseC, NumC(5), NumC(6))) is NumV(6)
  interp(IfC(StrC("true"), NumC(5), NumC(6))) raises "cond does not evaluate to boolean"
  interp(IdC("x")) raises "lookup: unbound identifier"
  interp(LetC("x", NumC(5), IdC("x"))) is NumV(5)
  interp(LetC("x", NumC(5), SeqC( SetC("x", NumC(8)) , IdC("x")))) is NumV(8)
  interp(ObjectC([fieldC("x", NumC(4)), fieldC("y", StrC("un estring"))])) is ObjectV([fieldV("y", StrV("un estring")), fieldV("x", NumV(4))])
  interp(GetFieldC(ObjectC([fieldC("x", NumC(4)), fieldC("y", StrC("un estring"))]), StrC("x"))) is NumV(4)
  interp(SetFieldC(ObjectC([fieldC("x", NumC(4))]), StrC("y"), StrC("un estring"))) is ObjectV([fieldV("y", StrV("un estring")), fieldV("x", NumV(4))])
  interp(SetFieldC(ObjectC([fieldC("x", NumC(4)), fieldC("y", NumC(8))]), StrC("y"), StrC("un estring"))) is ObjectV([fieldV("y", StrV("un estring")), fieldV("x", NumV(4))])
  interp(AppC(FuncC([], NumC(5)), [])) is NumV(5)
  interp(AppC(FuncC(["x"], NumC(5)), [StrC("un estring")])) is NumV(5)
  interp(AppC(FuncC(["x"], IdC("x")), [StrC("un estring")])) is StrV("un estring")
  interp(Prim1C("print", StrC("un estring"))) is StrV("un estring")
  interp(Prim1C("tagof", StrC("un estring"))) is StrV("string")
  interp(Prim1C("tagof", NumC(5))) is StrV("number")
  interp(Prim2C("num+", NumC(5), NumC(5))) is NumV(10)
  interp(Prim2C("num-", NumC(5), NumC(5))) is NumV(0)
  interp(Prim2C("string+", StrC("un"), StrC("estring"))) is StrV("unestring")
  interp(Prim2C("==", NumC(5), NumC(5))) is TrueV
  interp(Prim2C(">", NumC(5), NumC(5))) is FalseV
  interp(Prim2C("<", NumC(5), NumC(5))) is FalseV
  # IdC tests with direct interp-full
  interp-full(IdC("x"), [bind("x", 4)], [cell(4, NumV(6))]) is v-x-s(NumV(6), [cell(4, NumV(6))])
  interp-full(IdC("x"), [bind("x", 4)], [cell(3, NumV(6))]) raises "fetch: unbound location"
  interp-full(IdC("y"), [bind("x", 4)], [cell(4, NumV(6))]) raises "lookup: unbound identifier"
end


