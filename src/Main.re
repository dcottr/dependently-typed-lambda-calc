type term =
  | Annotation(term, term)
  | Star
  | Forall({
      argType: term,
      body: term,
    })
  | FreeVar(string)
  | BoundVar(int)
  | Application(term, term)
  | Function(term);

type value =
  | VStar
  | VFreeVar(string)
  | VApp(value, value)
  | VFunction(term, list(value))
  | VForall({
      argType: value,
      body: term,
      env: list(value),
    });

let identity =
  Annotation(
    Function(BoundVar(0)),
    Forall({argType: FreeVar("bool"), body: FreeVar("bool")}),
  );
let depTypedIdentity =
  Annotation(
    Function(Function(BoundVar(0))),
    Forall({
      argType: Star,
      body: Forall({argType: BoundVar(0), body: BoundVar(1)}),
    }),
  );

let prog =
  Application(
    Application(depTypedIdentity, FreeVar("bool")),
    FreeVar("x"),
  );
let prog = Application(depTypedIdentity, FreeVar("bool"));
// let const = Annotation(Function(Function(BoundVar(1))), Forall({argType: Star, }))

let rec termToStr = (~env=[], term) =>
  switch (term) {
  | Annotation(e, t) => termToStr(e) ++ "::" ++ termToStr(t)
  | Star => "*"
  | Forall({argType, body}) =>
    "∀" ++ termToStr(argType) ++ "." ++ termToStr(body)
  | FreeVar(name) => name
  | BoundVar(i) =>
    switch (List.nth_opt(env, max(0, i - 1))) {
    | Some(v) => valueToStr(v)
    | None => "bv(" ++ string_of_int(i) ++ ")"
    }
  | Application(func, arg) => termToStr(func) ++ " " ++ termToStr(arg)
  | Function(body) => "λ." ++ termToStr(body)
  }

and valueToStr = value =>
  switch (value) {
  | VStar => "*"
  | VFreeVar(s) => s
  | VApp(v1, v2) =>
    "vapp: ";
    valueToStr(v1) ++ " " ++ valueToStr(v2);
  | VFunction(term, env) => "λ." ++ termToStr(~env, term)
  | VForall({argType, body, env}) =>
    "∀" ++ valueToStr(argType) ++ "." ++ termToStr(~env, body)
  };

let rec evaluate = (term, env) =>
  switch (term) {
  | Annotation(e, _) => evaluate(e, env)
  | Star => VStar
  | Forall({argType, body}) =>
    VForall({argType: evaluate(argType, env), body, env})
  | FreeVar(x) => VFreeVar(x)
  | BoundVar(i) => List.nth(env, i)
  | Application(fn, arg) =>
    let fnVal = evaluate(fn, env);
    let argVal = evaluate(arg, env);
    switch (fnVal) {
    | VFunction(body, funEnv) => evaluate(body, [argVal, ...funEnv])
    | VApp(_)
    | VFreeVar(_) => VApp(fnVal, argVal)
    | _ => failwith("Tried to call something that wasn't a function.")
    };
  | Function(body) => VFunction(body, env)
  };

module StringMap = Map.Make(String);

let rec checkType = (e, t, context, env) =>
  switch (e) {
  | Function(body) =>
    switch (t) {
    | VForall({argType, body: forallBody, env}) =>
      let extendedEnv = [argType, ...env];
      checkType(
        body,
        evaluate(forallBody, extendedEnv),
        context,
        extendedEnv,
      );
    | v => failwith("Expected function type but got " ++ valueToStr(v))
    }
  | e =>
    let synthType = synthesizeType(e, context, env);
    if (synthType != t) {
      failwith(
        "Expected type "
        ++ valueToStr(t)
        ++ " but got "
        ++ valueToStr(synthType),
      );
    };
  }

// Context is the free variable to type mapping, and env is the bound variable to typ mapping (with Bruijn indexing).
and synthesizeType = (e, context, env) =>
  switch (e) {
  | Annotation(e, t) =>
    checkType(t, VStar, context, env);

    let tVal = evaluate(t, []);

    checkType(e, tVal, context, env);
    tVal;
  | Star => VStar
  | Forall({argType, body}) =>
    checkType(argType, VStar, context, env);
    let tau = evaluate(argType, env);

    checkType(body, VStar, context, [tau, ...env]);
    VStar;
  | FreeVar(name) =>
    switch (StringMap.find_opt(name, context)) {
    | Some(t) => t
    | None => failwith("Used variable with unknown type " ++ name)
    }
  | BoundVar(i) => List.nth(env, i)
  | Application(func, arg) =>
    let funcType = synthesizeType(func, context, env);
    switch (funcType) {
    | VForall({argType, body, env}) =>
      checkType(arg, argType, context, env);
      evaluate(body, [evaluate(arg, env), ...env]);
    | v => failwith("Can't apply non-function " ++ valueToStr(v))
    };
  | Function(body) =>
    failwith("Couldn't determine type of function " ++ termToStr(e))
  };

let map = StringMap.empty;
let map = StringMap.add("bool", VStar, map);
let map = StringMap.add("x", VFreeVar("bool"), map);

print_endline(valueToStr(synthesizeType(depTypedIdentity, map, [])));
print_endline(valueToStr(synthesizeType(prog, map, [])));

// TODO: test annotating with the type being a bound variable. See if the evaluate with [] env works.
