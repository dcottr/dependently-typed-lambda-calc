
type term =
  | Annotation(term, term)
  | Star
  | Forall({argType: term, body: term})
  | FreeVar(string)
  | BoundVar(int)
  | Application(term, term)
  | Function(term)

type value =
  | VStar
  | VFreeVar(string)
  | VApp(value, value)
  | VFunction(term)
  | VForall({argType: value, body: term})

let identity = Annotation(Function(BoundVar(0)), Forall({argType: FreeVar("a"), body: FreeVar("a")}))
let depTypedIdentity = Annotation(Function(Function(BoundVar(0))), Forall({argType: Star, body: Forall({argType: BoundVar(0), body: BoundVar(1)})}))

let prog = Application(Application(depTypedIdentity, FreeVar("bool")), FreeVar("x"))
// let const = Annotation(Function(Function(BoundVar(1))), Forall({argType: Star, }))

let rec termToStr = (term) =>
  switch(term) {
  | Annotation(e, t) => termToStr(e) ++ "::" ++ termToStr(t)
  | Star => "*"
  | Forall({argType, body}) => "∀" ++ termToStr(argType) ++ "." ++ termToStr(body)
  | FreeVar(name) => name
  | BoundVar(i) => "bv(" ++ string_of_int(i) ++ ")"
  | Application(func, arg) => termToStr(func) ++ " " ++ termToStr(arg)
  | Function(body) => "λ." ++ termToStr(body)
}

let rec valueToStr = (value) =>
  switch(value) {
  | VStar => "*"
  | VFreeVar(s) => s
  | VApp(v1, v2) => valueToStr(v1) ++ " " ++ valueToStr(v2)
  | VFunction(term) => "λ." ++ termToStr(term)
  | VForall({argType, body}) => "∀" ++ valueToStr(argType) ++ "." ++ termToStr(body)
}

let rec evaluate = (term, env) =>
  switch (term) {
    | Annotation(e, _) => evaluate(e, env)
    | Star => VStar
    | Forall({argType, body}) =>
      VForall({argType: evaluate(argType, env), body})
    | FreeVar(x) => VFreeVar(x)
    | BoundVar(i) =>
      List.nth(env, i)
    | Application(fn, arg) =>
      let fnVal = evaluate(fn, env)
      let argVal = evaluate(arg, env)
      switch(fnVal) {
        | VFunction(body) =>
          evaluate(body, [argVal,  ...env])
        | VApp(_)
        | VFreeVar(_) =>
          VApp(fnVal, argVal)
        | _ => failwith("Tried to call something that wasn't a function.")
      }
    | Function(body) =>
      VFunction(body)
  }

print_endline(valueToStr(evaluate(prog, [])))
print_endline(termToStr(prog))