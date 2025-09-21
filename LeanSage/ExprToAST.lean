import LeanSage.Core

open Lean Meta

namespace LeanSage

def unwrapApps (expr : Expr) : Expr × List Expr :=
  let rec go (e : Expr) (args : List Expr) : Expr × List Expr :=
    match e with
    | .app f arg => go f (arg :: args)
    | _ => (e, args)
  go expr []

def unaryFunctions : List (String × String) := [
  ("Real.sqrt", "sqrt"), ("Real.sin", "sin"), ("Real.cos", "cos"),
  ("Real.tan", "tan"), ("Real.exp", "exp"), ("Real.log", "log"),
  ("Complex.exp", "exp"), ("Complex.sin", "sin"), ("Complex.cos", "cos"),
  ("Complex.tan", "tan"), ("Complex.log", "log"),
  ("Nat.factorial", "factorial"), ("Nat.Prime", "is_prime"),
  ("Nat.primeFactors", "prime_factors"), ("Nat.divisors", "divisors"),
  ("Nat.totient", "euler_phi"), ("Int.natAbs", "abs"),
  ("Complex.re", "real"), ("Complex.im", "imag"),
  ("String.length", "length"), ("Array.size", "length"),
  ("List.length", "length"), ("Finset.card", "length")
]

def binaryFunctions : List (String × String) := [
  ("Nat.gcd", "natGcd"), ("Int.gcd", "gcd"), ("Nat.lcm", "lcm"),
  ("Nat.choose", "binomial"), ("Nat.descFactorial", "falling_factorial"),
  ("Nat.ascFactorial", "rising_factorial"), ("List.append", "append"),
  ("HAppend.hAppend", "append")
]

def lookupUnaryFunc (name : String) : Option String :=
  unaryFunctions.lookup name

def lookupBinaryFunc (name : String) : Option String :=
  binaryFunctions.lookup name

mutual
  -- Lean Expr → MathAST translator
  partial def exprToAST (expr : Expr) : MetaM (Option MathAST) := do
    match expr with
    -- Basic constants
    | .const ``Nat.zero _ => return some (.nat 0)
    | .const ``Bool.true _ => return some (.bool true)
    | .const ``Bool.false _ => return some (.bool false)
    | .const ``Real.pi _ => return some .pi
    | .const ``Complex.I _ => return some .complexI

    -- Literals
    | .lit (.natVal n) => return some (.nat n)
    | .lit (.strVal s) => return some (.string s)

    -- Free variables
    | .fvar _ => do
      let fmt ← ppExpr expr
      let varName := fmt.pretty
      let typ ← inferType expr
      let typStr ← ppExpr typ
      return some (.var varName typStr.pretty)

    -- Bound variables - handled in lambda context
    | .bvar _ => return none

    -- Forall quantifier with multiple variables

    | .letE varName typ value body _ => do
      -- Substitute the value into the body (let reduction)
      withLocalDecl varName .default typ fun _localVar => do
        let bodyWithValue := body.instantiate1 value
        exprToAST bodyWithValue

    -- Lambda functions
    | .lam varName varTyp body _ => do
      withLocalDecl varName .default varTyp fun localVar => do
        let bodyWithVar := body.instantiate1 localVar
        if let some bodyAST ← exprToAST bodyWithVar then
          let some varTypAST ← exprToAST varTyp | return none
          return some (.lambda varName.toString varTypAST bodyAST)
        else
          return none

    | _ =>
      let (head, args) := unwrapApps expr

      -- Debug head and num args
      -- logInfo s!"Head: {head}, NumArgs: {args.length}"

      match head, args with
      -- Equality
      | .const ``Eq _, [_, lhs, rhs] => do
        let some lhsAST ← exprToAST lhs | return none
        let some rhsAST ← exprToAST rhs | return none
        return some (.eq lhsAST rhsAST)

      -- OfNat patterns
      | .const ``OfNat.ofNat _, [.const ``Rat _, .lit (.natVal n), _] =>
        return some (.rat (n : Int) 1)
      | .const ``OfNat.ofNat _, [.const ``Fin _, .lit (.natVal mod), _, .lit (.natVal n), _] =>
        return some (.mod (.nat n) (.nat mod))
      | .const ``OfNat.ofNat _, [typ, .lit (.natVal n), _] => do
        let (typHead, _) := unwrapApps typ
        match typHead with
        | .const ``Matrix _ =>
          if n == 1 then
            return some (.func "identity_matrix" [])
          else
            return some (.nat n)
        | _ => return some (.nat n)
      | .const ``OfNat.ofNat _, [_, .lit (.natVal n), _, _] => return some (.nat n)

      -- Integer operations
      | .const ``Int.negOfNat _, [n] => do
        let some nAST ← exprToAST n | return none
        match nAST with
        | .nat val => return some (.int (-(val : Int)))
        | _ => return some (.neg nAST)
      | .const ``Int.ofNat _, [n] => do
        let some nAST ← exprToAST n | return none
        return some nAST

      -- Natural number operations
      | .const ``Nat.succ _, [n] => do
        let some nAST ← exprToAST n | return none
        return some (.add [nAST, .nat 1])

      -- Negation & abs
      | .const ``Neg.neg _, [_, _, x] => do
        let some xAST ← exprToAST x | return none
        return some (.neg xAST)
      | .const ``abs _, [x] => do
        let some xAST ← exprToAST x | return none
        return some (.abs xAST)

      -- Fin arithmetic
      | .const ``HAdd.hAdd _, [.app (.const ``Fin _) modulus, _, _, _, a, b] => do
        let some aAST ← exprToAST a | return none
        let some bAST ← exprToAST b | return none
        let some modAST ← exprToAST modulus | return none
        return some (.mod (.add [aAST, bAST]) modAST)
      | .const ``HMul.hMul _, [.app (.const ``Fin _) modulus, _, _, _, a, b] => do
        let some aAST ← exprToAST a | return none
        let some bAST ← exprToAST b | return none
        let some modAST ← exprToAST modulus | return none
        return some (.mod (.mul [aAST, bAST]) modAST)
      | .const ``HSub.hSub _, [.app (.const ``Fin _) modulus, _, _, _, a, b] => do
        let some aAST ← exprToAST a | return none
        let some bAST ← exprToAST b | return none
        let some modAST ← exprToAST modulus | return none
        return some (.mod (.sub aAST bAST) modAST)

      -- Boolean operations
      | .const ``Not _, [a] => do
        let some aAST ← exprToAST a | return none
        return some (.not aAST)

      -- Rational number operations
      | .const ``Rat.num _, [rat] => do
        let some ratAST ← exprToAST rat | return none
        match ratAST with
        | .rat num _ => return some (.int num)
        | _ => return some (.func "numer" [ratAST])
      | .const ``Rat.den _, [rat] => do
        let some ratAST ← exprToAST rat | return none
        match ratAST with
        | .rat _ den => return some (.nat den)
        | _ => return some (.func "denom" [ratAST])

      -- Complex operations
      | .const ``Complex.ofReal _, [x] => do
        let some xAST ← exprToAST x | return none
        return some (.complex xAST (.nat 0))

      -- List operations
      | .const ``List.nil _, [_] => return some (.list [])
      | .const ``List.cons _, [_, head, tail] => do
        let some headAST ← exprToAST head | return none
        let some tailAST ← exprToAST tail | return none
        match tailAST with
        | .list elems => return some (.list (headAST :: elems))
        | _ => return some (.func "cons" [headAST, tailAST])

      -- Array operations
      | .const ``Array.mk _, [_, list] => do
        let some listAST ← exprToAST list | return none
        return some listAST
      | .const ``List.toArray _, [_, list] => do
        let some listAST ← exprToAST list | return none
        return some listAST

      -- Pair/Product types
      | .const ``Prod.mk _, [_, _, a, b] => do
        let some aAST ← exprToAST a | return none
        let some bAST ← exprToAST b | return none
        return some (.tuple [aAST, bAST])
      | .const ``Prod.fst _, [_, _, pair] => processUnaryFunc pair "fst"
      | .const ``Prod.snd _, [_, _, pair] => processUnaryFunc pair "snd"

      -- Set operations
      | .const ``Membership.mem _, [_, _, _, elem, set] => do
        let some elemAST ← exprToAST elem | return none
        let some setAST ← exprToAST set | return none
        match elemAST, setAST with
        | .ideal _ _, _ => return some (.membership setAST elemAST)
        | _, .ideal _ _ => return some (.membership elemAST setAST)
        | _, _ => return some (.membership elemAST setAST)
      | .const ``Insert.insert _, [_, _, _, elem, rest] => do
        let some elemAST ← exprToAST elem | return none
        let some restAST ← exprToAST rest | return none
        match restAST with
        | .set elems => return some (.set (elemAST :: elems))
        | .singleton elem2 => return some (.set [elemAST, elem2])
        | _ =>
          let rec extractSetElements (expr : Expr) : MetaM (List MathAST) := do
            let (head, args) := unwrapApps expr
            match head, args with
            | .const ``Insert.insert _, [_, _, _, elem, rest] => do
              let some elemAST ← exprToAST elem | return []
              let restElems ← extractSetElements rest
              return elemAST :: restElems
            | .const ``Singleton.singleton _, [_, _, _, elem] => do
              let some elemAST ← exprToAST elem | return []
              return [elemAST]
            | .const ``EmptyCollection.emptyCollection _, _ => return []
            | _, _ => return []

          let elems ← extractSetElements expr
          return some (.set elems)
      | .const ``Singleton.singleton _, [_, _, _, elem] => do
        let some elemAST ← exprToAST elem | return none
        return some (.singleton elemAST)

      -- Empty sets
      | .const ``EmptyCollection.emptyCollection _, [_, _] => return some .emptySet

      -- Intervals
      | .const ``Set.Icc _, [_, _, a, b] => do
        let some aAST ← exprToAST a | return none
        let some bAST ← exprToAST b | return none
        return some (.interval aAST bAST false false)  -- closed
      | .const ``Set.Ioo _, [_, _, a, b] => do
        let some aAST ← exprToAST a | return none
        let some bAST ← exprToAST b | return none
        return some (.interval aAST bAST true true)   -- open
      | .const ``Set.Ico _, [_, _, a, b] => do
        let some aAST ← exprToAST a | return none
        let some bAST ← exprToAST b | return none
        return some (.interval aAST bAST false true)  -- left-closed, right-open
      | .const ``Set.Ioc _, [_, _, a, b] => do
        let some aAST ← exprToAST a | return none
        let some bAST ← exprToAST b | return none
        return some (.interval aAST bAST true false)  -- left-open, right-closed
      | .const ``Ideal.span _, [ring, _, generators] => do
        let some genAST ← exprToAST generators | return none
        let ringType ← inferType ring
        let (ringHead, _) := unwrapApps ringType
        let ringName := match ringHead with
          | .const ``Int _ => "Int"
          | .const ``Rat _ => "Rat"
          | .const ``Real _ => "Real"
          | _ => "Int"  -- default
        return some (.ideal ringName [genAST])
      | .const ``Ideal.radical _, [_, _, ideal] => do
        let some idealAST ← exprToAST ideal | return none
        return some (.func "radical" [idealAST])

      -- Quantifiers - handle exists with multiple variables
      | .const ``Exists _, [typ, .lam varName _ body _] => do
        -- Use withLocalDecl to handle bound variables properly
        let rec processExists (vars : List (String × MathAST)) (expr : Expr) : MetaM (List (String × MathAST) × Option MathAST) := do
          match expr with
          | .app (.app (.const ``Exists _) nextTyp) (.lam nextVarName _ nextBody _) => do
            let some nextTypAST ← exprToAST nextTyp | return (vars, none)
            -- Recursively process nested exists
            withLocalDecl nextVarName .default nextTyp fun nextLocalVar => do
              let nextBodyWithVar := nextBody.instantiate1 nextLocalVar
              processExists (vars ++ [(nextVarName.toString, nextTypAST)]) nextBodyWithVar
          | _ => do
            -- No more nested exists, process the final body
            let bodyAST ← exprToAST expr
            return (vars, bodyAST)

        let some typAST ← exprToAST typ | return none
        -- Start processing with the first variable
        withLocalDecl varName .default typ fun localVar => do
          let bodyWithVar := body.instantiate1 localVar
          let (allVars, some bodyAST) ← processExists [(varName.toString, typAST)] bodyWithVar | return none
          return some (.exists allVars bodyAST)

      -- Polynomial operations
      | .const ``Polynomial.X _, _ => return some (.polynomialVar "X")
      | .const ``Polynomial.C _, [_, _, c] => do
        let some cAST ← exprToAST c | return none
        return some (.polynomialC cAST)
      | .const ``Polynomial.monomial _, [_, _, deg, coeff] => do
        let some degAST ← exprToAST deg | return none
        let some coeffAST ← exprToAST coeff | return none
        return some (.monomial "X" degAST coeffAST)
      | .const ``Polynomial.eval _, [_, _, x, p] => processBinaryFunc p x "eval"
      | .const ``Polynomial.eval₂ _, args => do
        if args.length >= 3 then
          let x := args[args.length - 2]!
          let p := args[args.length - 1]!
          let some pAST ← exprToAST p | return none
          let some xAST ← exprToAST x | return none
          return some (.func "eval" [pAST, xAST])
        else
          return none

      | .const ``Polynomial.degree _, args => do
        if args.length >= 1 then
          let p := args[args.length - 1]!
          processUnaryFunc p "degree"
        else
          return none
      | .const ``Polynomial.natDegree _, args => do
        match args with
        | [_, _, p] => processUnaryFunc p "degree"
        | _ => return none
      | .const ``Polynomial.leadingCoeff _, args => do
        match args with
        | [_, _, p] => processUnaryFunc p "leadingCoeff"
        | _ => return none
      | .const ``Polynomial.derivative _, args => do
        match args with
        | [_, _, p] => processUnaryFunc p "polyDerivative"
        | _ => return none
      | .const ``Polynomial.factor _, args => do
        match args with
        | [_, _, p] => processUnaryFunc p "factor"
        | _ => return none
      | .const ``Polynomial.roots _, args => do
        match args with
        | [_, _, _, p] => processUnaryFunc p "roots"
        | _ => return none
      | .const ``Polynomial.coeff _, args => do
        match args with
        | [_, _, p, n] => processBinaryFunc p n "coeff"
        | _ => return none

      -- Derivatives
      | .const ``deriv _, args => do
        match args with
        | [_, _, _, _, _, _, f, x] => do
          let some fAST ← exprToAST f | return none
          let some xAST ← exprToAST x | return none
          match fAST, xAST with
          | .lambda varName _ bodyAST, .var _ _ =>
            return some (.derivative bodyAST varName 1)
          | .lambda varName _ bodyAST, _ =>
            let derivAST := .derivative bodyAST varName 1
            return some (.func "subs" [derivAST, .eq (.var varName "Real") xAST])
          | _, .var varName _ =>
            return some (.derivative fAST varName 1)
          | _, _ =>
            let derivAST := .derivative fAST "x" 1
            return some (.func "subs" [derivAST, .eq (.var "x" "Real") xAST])
        | _ => return none    -- Multivariable derivatives
      | .const ``fderiv _, args => do
        match args with
        | [_, _, _, _, _, _, _, _, _, _, f, x] => do
          let some fAST ← exprToAST f | return none
          let some xAST ← exprToAST x | return none
          match fAST, xAST with
          | .lambda varName _ bodyAST, .var _ _ =>
            return some (.derivative bodyAST varName 1)
          | .lambda varName _ bodyAST, _ =>
            let derivAST := .derivative bodyAST varName 1
            return some (.func "subs" [derivAST, .eq (.var varName "Real") xAST])
          | _, .var varName _ =>
            return some (.derivative fAST varName 1)
          | _, _ =>
            let derivAST := .derivative fAST "x" 1
            return some (.func "subs" [derivAST, .eq (.var "x" "Real") xAST])
        | _ => return none

      -- Higher-order derivatives
      | .const ``iteratedDeriv _, args => do
        match args with
        | [_, _, _, _, _, _, n, f, x] => do
          let some nAST ← exprToAST n | return none
          let some fAST ← exprToAST f | return none
          let some xAST ← exprToAST x | return none
          match fAST, nAST, xAST with
          | .lambda varName _ bodyAST, .nat order, .var _ _ =>
            return some (.derivative bodyAST varName order)
          | .lambda varName _ bodyAST, .nat order, _ =>
            let derivAST := .derivative bodyAST varName order
            return some (.func "subs" [derivAST, .eq (.var varName "Real") xAST])
          | _, .nat order, .var varName _ =>
            return some (.derivative fAST varName order)
          | _, .nat order, _ =>
            let derivAST := .derivative fAST "x" order
            return some (.func "subs" [derivAST, .eq (.var "x" "Real") xAST])
          | _, _, _ =>
            -- For non-natural number orders, fall back to .func representation
            return some (.func "diff" [fAST, xAST, nAST])
        | [_, _, _, _, _, n, f, x] => do
          let some nAST ← exprToAST n | return none
          let some fAST ← exprToAST f | return none
          let some xAST ← exprToAST x | return none
          match fAST, nAST, xAST with
          | .lambda varName _ bodyAST, .nat order, .var _ _ =>
            return some (.derivative bodyAST varName order)
          | .lambda varName _ bodyAST, .nat order, _ =>
            let derivAST := .derivative bodyAST varName order
            return some (.func "subs" [derivAST, .eq (.var varName "Real") xAST])
          | _, .nat order, .var varName _ =>
            return some (.derivative fAST varName order)
          | _, .nat order, _ =>
            let derivAST := .derivative fAST "x" order
            return some (.func "subs" [derivAST, .eq (.var "x" "Real") xAST])
          | _, _, _ =>
            -- For non-natural number orders, fall back to .func representation
            return some (.func "diff" [fAST, xAST, nAST])
        | _ => return none

      -- Integrals
      | .const ``intervalIntegral _, args => do
        if args.length >= 4 then
          let f := args[args.length - 4]!
          let a := args[args.length - 3]!
          let b := args[args.length - 2]!

          let some fAST ← exprToAST f | return none
          let some aAST ← exprToAST a | return none
          let some bAST ← exprToAST b | return none

          match fAST with
          | .lambda varName _ bodyAST =>
            return some (.integral bodyAST varName (some aAST) (some bAST))
          | _ =>
            return some (.integral fAST "x" (some aAST) (some bAST))
        else
          return none

      -- Volume integrals (indefinite integrals)
      | .const ``MeasureTheory.integral _, args => do
        let rec findLambda (args : List Expr) : MetaM (Option MathAST) := do
          match args with
          | [] => return none
          | arg :: rest =>
            match ← exprToAST arg with
            | some (.lambda varName _ bodyAST) =>
              return some (.integral bodyAST varName none none)
            | _ => findLambda rest
        findLambda args

      -- Matrix operations
      | .const ``Matrix.det _, [_, _, _, _, _, M] => processUnaryFunc M "det"
      | .const ``Matrix.trace _, [_, _, _, _, M] => processUnaryFunc M "trace"
      | .const ``Matrix.transpose _, [_, _, _, M] => processUnaryFunc M "transpose"
      | .const ``Matrix.rank _, [_, _, _, _, _, M] => processUnaryFunc M "rank"
      | .const ``Matrix.charpoly _, [_, _, _, _, _, M] => processUnaryFunc M "charpoly"
      | .const ``Inv.inv _, [_, _, M] => processUnaryFunc M "inverse"

      -- Matrix vecCons/vecEmpty construction
      | .const ``Matrix.vecCons _, [_, _, elem, rest] => do
        let some elemAST ← exprToAST elem | return none
        let some restAST ← exprToAST rest | return none
        match restAST with
        | .list elems => return some (.list (elemAST :: elems))
        | _ => return some (.list [elemAST])

      | .const ``Matrix.vecEmpty _, [_] => return some (.list [])

      -- DFunLike.coe - handle both matrix and polynomial coercions
      | .const ``DFunLike.coe _, args => do
        for arg in args do
          let (argHead, _argArgs) := unwrapApps arg
          match argHead with
          | .const ``Polynomial.C _ =>
            if args.length >= 1 then
              let coeff := args[args.length - 1]!
              let some coeffAST ← exprToAST coeff | return none
              return some (.polynomialC coeffAST)
          | .const ``Polynomial.derivative _ =>
            if args.length >= 1 then
              let poly := args[args.length - 1]!
              let some polyAST ← exprToAST poly | return none
              return some (.func "polyDerivative" [polyAST])
          | .const ``Matrix.of _ =>
            for dataArg in args do
              if dataArg != arg then
                let rec extractMatrix2 (e : Expr) : MetaM (Option (List (List MathAST))) := do
                  match e with
                  | .app (.app (.app (.app (.const ``Matrix.vecCons _) _) _) row) rest => do
                    let rec extractRow (rowExpr : Expr) : MetaM (Option (List MathAST)) := do
                      match rowExpr with
                      | .app (.app (.app (.app (.const ``Matrix.vecCons _) _) _) elem) rowRest => do
                        let some elemAST ← exprToAST elem | return none
                        let some restElems ← extractRow rowRest | return none
                        return some (elemAST :: restElems)
                      | .app (.const ``Matrix.vecEmpty _) _ => return some []
                      | _ => return none
                    let some rowElems ← extractRow row | return none
                    let some restMatrix ← extractMatrix2 rest | return none
                    return some (rowElems :: restMatrix)
                  | .app (.const ``Matrix.vecEmpty _) _ => return some []
                  | _ => return none

                match ← extractMatrix2 dataArg with
                | some matrix => return some (.matrix matrix)
                | none => continue
          | _ => continue

        -- If matrix extraction failed, try general coercion handling
        if args.length >= 3 then
          -- Try to process the actual value being coerced (usually the last argument)
          let value := args[args.length - 1]!
          exprToAST value
        else
          return none

      -- Matrix construction patterns
      | .const ``Matrix.of _, args => do
        if args.length >= 1 then
          let data := args[args.length - 1]!

          let extractRow (rowExpr : Expr) : MetaM (List MathAST) := do
            let rec collectElems (e : Expr) (acc : List MathAST) : MetaM (List MathAST) := do
              match e with
              | .app (.app (.app (.app (.const ``Matrix.vecCons _) _) _) elem) rowRest => do
                let some elemAST ← exprToAST elem | return acc.reverse
                collectElems rowRest (elemAST :: acc)
              | .app (.const ``Matrix.vecEmpty _) _ => return acc.reverse
              | _ =>
                match ← exprToAST e with
                | some elemAST => return (elemAST :: acc).reverse
                | none => return acc.reverse
            collectElems rowExpr []

          let extractMatrix (e : Expr) : MetaM (Option (List (List MathAST))) := do
            let rec collectRows (expr : Expr) (acc : List (List MathAST)) : MetaM (Option (List (List MathAST))) := do
              match expr with
              | .app (.app (.app (.app (.const ``Matrix.vecCons _) _) _) row) rest => do
                let rowData ← extractRow row
                collectRows rest (rowData :: acc)
              | .app (.const ``Matrix.vecEmpty _) _ => return some acc.reverse
              | _ => return none
            collectRows e []

          match ← extractMatrix data with
          | some matrixData => return some (.matrix matrixData)
          | none => return none
        else
          return none

      -- Unary functions
      | .const name _, [x] =>
        if let some funcName := lookupUnaryFunc name.toString then
          processUnaryFunc x funcName
        else
          -- Handle special cases that don't follow the pattern
          match name.toString with
          | "Neg.neg" => do
            let some xAST ← exprToAST x | return none
            return some (.neg xAST)
          | "abs" => do
            let some xAST ← exprToAST x | return none
            return some (.abs xAST)
          | "Not" => do
            let some xAST ← exprToAST x | return none
            return some (.not xAST)
          | _ => return none

      -- Binary functions
      | .const name _, [a, b] =>
        let stringName := name.toString
        if let some funcName := lookupUnaryFunc stringName then
          processUnaryFunc b funcName
        else if let some funcName := lookupBinaryFunc stringName then
          processBinaryFunc a b funcName
        else
          match stringName with
          | "HAdd.hAdd" => processBinaryListOp a b MathAST.add
          | "HMul.hMul" => processBinaryListOp a b MathAST.mul
          | "HDiv.hDiv" => processBinaryOp a b MathAST.div
          | "HSub.hSub" => processBinaryOp a b MathAST.sub
          | "HPow.hPow" => processBinaryOp a b MathAST.pow
          | "HMod.hMod" => processBinaryOp a b MathAST.mod
          | "And" => processBinaryListOp a b MathAST.and
          | "Or" => processBinaryListOp a b MathAST.or
          | "Union.union" => processBinaryOp a b MathAST.union
          | "Inter.inter" => processBinaryOp a b MathAST.intersection
          | "SDiff.sdiff" => processBinaryOp a b MathAST.setDiff
          | "HasSubset.Subset" => processBinaryOp a b MathAST.subset
          | "Complex.mk" => processBinaryOp a b MathAST.complex
          | _ => return none

      | .const name _, [_, _, a, b] =>
        match name.toString with
        | "LT.lt" => processBinaryOp a b MathAST.lt
        | "LE.le" => processBinaryOp a b MathAST.le
        | "GT.gt" => processBinaryOp a b MathAST.gt
        | "GE.ge" => processBinaryOp a b MathAST.ge
        | "Union.union" => processBinaryOp a b MathAST.union
        | "Inter.inter" => processBinaryOp a b MathAST.intersection
        | "SDiff.sdiff" => processBinaryOp a b MathAST.setDiff
        | "HasSubset.Subset" => processBinaryOp a b MathAST.subset
        | _ => return none

      | .const name _, [_, _, _, _, a, b] =>
        match name.toString with
        | "HAdd.hAdd" => processBinaryListOp a b MathAST.add
        | "HMul.hMul" => processBinaryListOp a b MathAST.mul
        | "HDiv.hDiv" => processBinaryOp a b MathAST.div
        | "HSub.hSub" => processBinaryOp a b MathAST.sub
        | "HPow.hPow" => processBinaryOp a b MathAST.pow
        | "HMod.hMod" => processBinaryOp a b MathAST.mod
        | "HAppend.hAppend" => processBinaryFunc a b "append"
        | _ => return none

      -- Constants - map to function calls for specialized operations
      | .const name _, args => do
        if name == `True then
          return some (.bool true)
        else if name == `False then
          return some (.bool false)
        else do
          let argASTs ← args.mapM exprToAST
          let validArgs := argASTs.filterMap id
          if validArgs.length == argASTs.length then
            return some (.func name.toString validArgs)
          else
            return none

      -- General function application
      | _, [arg] => do
        let some headAST ← exprToAST head | return none
        let some argAST ← exprToAST arg | return none
        match headAST with
        | .var "derivative" _ =>
          return some (.func "polyDerivative" [argAST])
        | .lambda _ _ _ =>
          return some (.apply headAST [argAST])
        | .func name existing_args =>
          return some (.func name (existing_args ++ [argAST]))
        | .var name _ =>
          return some (.func name [argAST])
        | _ =>
          return some (.apply headAST [argAST])

      -- Fallback
      | _, _ => return none

  partial def processBinaryOp (a b : Expr) (constructor : MathAST → MathAST → MathAST) : MetaM (Option MathAST) := do
    let some aAST ← exprToAST a | return none
    let some bAST ← exprToAST b | return none
    return some (constructor aAST bAST)

  partial def processBinaryListOp (a b : Expr) (constructor : List MathAST → MathAST) : MetaM (Option MathAST) := do
    let some aAST ← exprToAST a | return none
    let some bAST ← exprToAST b | return none
    return some (constructor [aAST, bAST])

  partial def processUnaryFunc (arg : Expr) (funcName : String) : MetaM (Option MathAST) := do
    let some argAST ← exprToAST arg | return none
    return some (.func funcName [argAST])

  partial def processBinaryFunc (a b : Expr) (funcName : String) : MetaM (Option MathAST) := do
    let some aAST ← exprToAST a | return none
    let some bAST ← exprToAST b | return none
    return some (.func funcName [aAST, bAST])

end

end LeanSage
