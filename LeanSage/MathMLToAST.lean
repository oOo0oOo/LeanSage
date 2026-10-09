import LeanSage.Core

namespace LeanSage

private inductive XMLNode where
  | element (tag : String) (children : List XMLNode)
  | text (content : String)
  | selfClosing (tag : String)

-- Advance slices through the input once instead of rescanning prefixes for each character.
private partial def parseNodes (input : String.Slice) (closing : Option String) :
    Option (List XMLNode × String.Slice) := do
  let mut rest := input.trimAscii
  let mut nodes : List XMLNode := []
  while !rest.isEmpty do
    if rest.startsWith "</" then
      let some tag := closing | failure
      unless rest.startsWith s!"</{tag}>" do failure
      return (nodes.reverse, rest)
    if rest.startsWith "<" then
      let tagPart := rest.drop 1 |>.takeWhile (· != '>')
      let tail := rest.dropWhile (· != '>')
      if tail.isEmpty then failure
      let afterTag := tail.drop 1
      let selfClosing := tagPart.endsWith "/"
      let namePart := if selfClosing then tagPart.dropEnd 1 else tagPart
      let tag := (namePart.takeWhile (!Char.isWhitespace ·)).toString
      if tag.isEmpty then failure
      if selfClosing then
        nodes := .selfClosing tag :: nodes
        rest := afterTag.trimAscii
      else
        let (children, close) ← parseNodes afterTag (some tag)
        nodes := .element tag children :: nodes
        rest := (close.drop (tag.length + 3)).trimAscii
    else
      let text := rest.takeWhile (· != '<')
      nodes := .text text.toString :: nodes
      rest := (rest.dropWhile (· != '<')).trimAscii
  if closing.isSome then failure
  return (nodes.reverse, rest)

private def parseXML (input : String) : Option (List XMLNode) := do
  let (nodes, _) ← parseNodes input.toSlice none
  return nodes

private def stringContains (s : String) (substr : String) : Bool :=
  (s.splitOn substr).length > 1

private def getLastAfterColon (s : String) : String :=
  match s.splitOn ":" with
  | [] => s
  | parts => parts.getLast!

private partial def xmlToAST (node : XMLNode) : Option MathAST :=
  match node with
  | XMLNode.text content =>
    if content.trimAscii.isEmpty then none  -- Filter out empty text
    else parseLeaf content.trimAscii.toString
  | XMLNode.selfClosing "pi" => some MathAST.pi
  | XMLNode.selfClosing "e" => some MathAST.e
  | XMLNode.selfClosing "imaginaryi" => some MathAST.complexI
  | XMLNode.selfClosing "int" => some (MathAST.string "int")
  | XMLNode.selfClosing tag =>
    if tag.trimAscii.isEmpty then none  -- Filter out empty tags
    else
      let result := some (MathAST.string tag)
      result
  | XMLNode.element tag children =>
    if tag.trimAscii.isEmpty then none  -- Filter out empty tags
    else
      let childASTs := children.filterMap xmlToAST
      match tag with
      | "math" | "mrow" | "item" =>
        match childASTs with
        | [single] =>
          some single
        | _ =>
          some (MathAST.list childASTs)

      -- Content MathML
      | "eq" | "plus" | "minus" | "times" | "divide" | "power" | "root" =>
        some (MathAST.string tag)
      | "apply" =>
        let (operators, operands) := childASTs.partition (fun ast =>
          match ast with
          | MathAST.string op => op ∈ ["eq", "plus", "minus", "times", "divide", "power", "root", "cos", "sin", "tan", "exp", "log", "ln", "si", "int"]
          | _ => false)
        match operators with
        | [MathAST.string op] =>
          let result := some (applyOperator op operands)
          result
        | _ =>
          none
      | "ci" =>
        let textContent := getTextContent children
        let result := some (MathAST.var textContent "Real")
        result
      | "cn" =>
        let textContent := getTextContent children
        let result := parseLeaf textContent
        result

      -- Presentation MathML
      | "mi" => some (MathAST.var (getTextContent children) "Real")
      | "mn" => parseLeaf (getTextContent children)
      | "mo" => some (MathAST.string (getTextContent children))
      | "mfrac" =>
        match childASTs with
        | [num, denom] => some (MathAST.div num denom)
        | _ => none
      | "msup" =>
        match childASTs with
        | [base, exp] => some (MathAST.pow base exp)
        | _ => none
      | "msqrt" =>
        match childASTs with
        | [arg] => some (MathAST.func "sqrt" [arg])
        | _ => none
      | "list" => some (MathAST.list childASTs)
      | "bvar" =>
        match childASTs with
        | [var] => some var
        | _ => none
      | "lowlimit" =>
        match childASTs with
        | [limit] => some limit
        | _ => none
      | "uplimit" =>
        match childASTs with
        | [limit] => some limit
        | _ => none
      | _ =>
        if stringContains tag ":" then
          let cleanTag := getLastAfterColon tag
          match cleanTag with
          | "mi" => some (MathAST.var (getTextContent children) "Real")
          | "mn" => parseLeaf (getTextContent children)
          | "mo" => some (MathAST.string (getTextContent children))
          | "msub" =>
            -- Handle subscripted variables like t_0 -> "t0"
            match childASTs with
            | [MathAST.var base _, MathAST.nat idx] => some (MathAST.var s!"{base}{idx}" "Real")
            | [MathAST.var base _, MathAST.var idx _] => some (MathAST.var s!"{base}_{idx}" "Real")
            | _ => some (MathAST.list childASTs)
          | _ =>
            if childASTs.length == 1 then childASTs.head?
            else if childASTs.isEmpty then none
            else some (MathAST.list childASTs)
        else
          dbg_trace s!"Unknown tag '{tag}' with {childASTs.length} children"
          if childASTs.length == 1 then childASTs.head?
          else if childASTs.isEmpty then none
          else some (MathAST.list childASTs)

where
  parseLeaf (s : String) : Option MathAST :=
    if s == "True" then some (MathAST.bool true)
    else if s == "False" then some (MathAST.bool false)
    else if s == "π" || s == "pi" then some MathAST.pi
    else if s == "imaginaryi" then some MathAST.complexI
    else if s == "e" then some MathAST.e
    else if let some n := s.toNat? then some (MathAST.nat n)
    else if let some i := s.toInt? then some (MathAST.int i)
    else if s.length == 1 && s.all Char.isAlpha then some (MathAST.var s "Real")
    else some (MathAST.string s)

  getTextContent (nodes : List XMLNode) : String :=
    String.join (nodes.map fun node =>
      match node with
      | XMLNode.text s => s.trimAscii.toString
      | XMLNode.element tag children =>
        if stringContains tag ":" then
          let cleanTag := getLastAfterColon tag
          match cleanTag with
          | "mi" | "mn" => getTextContent children
          | "msub" =>
            -- Convert t_0 to "t0"
            match children with
            | [baseNode, idxNode] =>
              let base := getTextContent [baseNode]
              let idx := getTextContent [idxNode]
              s!"{base}{idx}"
            | _ => ""
          | _ => ""
        else ""
      | _ => "")

  applyOperator (op : String) (operands : List MathAST) : MathAST :=
    match op, operands with
    | "eq", [a, b] => MathAST.eq a b
    | "plus", [] => MathAST.nat 0
    | "plus", [x] => x
    | "plus", args => MathAST.add args
    | "times", [] => MathAST.nat 1
    | "times", [x] => x
    | "times", args =>
      let hasVar := args.any (fun ast => match ast with | MathAST.var _ _ => true | _ => false)
      if hasVar then MathAST.mul args else MathAST.mul args
    | "minus", [x] => MathAST.neg x
    | "minus", [x, y] => MathAST.sub x y
    | "minus", args =>
      -- Handle multiple operands: a - b - c = a - (b + c)
      match args with
      | [] => MathAST.nat 0
      | [x] => MathAST.neg x
      | x :: rest => MathAST.sub x (MathAST.add rest)
    | "divide", [x] => MathAST.div x (MathAST.nat 1)
    | "divide", [x, y] => MathAST.div x y
    | "power", [x, y] => MathAST.pow x y
    | "root", [x] => MathAST.func "sqrt" [x]
    | "cos", [x] => MathAST.func "cos" [x]
    | "sin", [x] => MathAST.func "sin" [x]
    | "tan", [x] => MathAST.func "tan" [x]
    | "exp", [x] => MathAST.func "exp" [x]
    | "log", [x] => MathAST.func "log" [x]
    | "ln", [x] => MathAST.func "ln" [x]
    | "int", operands =>
      -- Handle integral: int, bvar, lowlimit, uplimit, integrand
      let rec extractIntegralParts (ops : List MathAST) (var : Option MathAST) (lower : Option MathAST) (upper : Option MathAST) (integrand : Option MathAST) : MathAST :=
        match ops with
        | [] =>
          match var, lower, upper, integrand with
          | some (MathAST.var varName _), some lowerVal, some upperVal, some expr =>
            MathAST.integral expr varName (some lowerVal) (some upperVal)
          | some (MathAST.var varName _), none, none, some expr =>
            MathAST.integral expr varName none none
          | _, _, _, some expr => expr
          | _, _, _, none => MathAST.string "error"
        | op :: rest =>
          match op with
          | MathAST.var _ _ => extractIntegralParts rest (some op) lower upper integrand
          | _ =>
            if lower.isNone then extractIntegralParts rest var (some op) upper integrand
            else if upper.isNone then extractIntegralParts rest var lower (some op) integrand
            else extractIntegralParts rest var lower upper (some op)
      extractIntegralParts operands none none none none
    | _, _ =>
      dbg_trace s!"Unknown operator '{op}' with {operands.length} operands: {repr operands}"
      MathAST.string "error"

-- Main entry point
partial def mathMLToAST (input : String) : Option MathAST := do
  let nodes ← parseXML input
  match nodes with
  | [single] => xmlToAST single
  | multiple => some (MathAST.list (multiple.filterMap xmlToAST))

end LeanSage
