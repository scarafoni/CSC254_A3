(*******************************************************************************)
(*                                                                             *) 
(*  LL parser in OCaml (based on the LL parser in Haskell and Scheme).         *)
(*                                                                             *) 
(*  Written by Michael L. Scott for CSC 254, September 2004.                   *)
(*  Translated to ocaml by Ryan Yates for CSC 254, September 2013.             *)
(*  Modified and extended, September 2005, 2006, 2008, 2009, and 2011--2013.   *)
(*                                                                             *) 
(*  To test this code, load it into ocaml with ocaml -init LLParse.ml          *)
(*  and type, e.g.                                                             *)
(*                                                                             *) 
(*  # let prog = "read a read b sum := a + b write sum write sum / 2";;        *)
(*  # parse (makeParseTable calcGrammar) prog;;                                *)
(*                                                                             *) 
(*  Note that the input program is a list of strings.                          *)
(*                                                                             *) 
(*  Note, also, that nothing in this file is input-language-specific,          *)
(*  other than sample grammars and inputs.  For the assignment you'll          *)
(*  need to add language-specific code to convert the parse tree into an       *)
(*  abstract syntax tree, to enforce semantic rules (if any), and to           *)
(*  interpret program input.                                                   *)
(*                                                                             *) 
(*******************************************************************************)

(*
   This first section of the file contains utility routines that you may
   find helpful.  I recommend you read all the routines carefully.
   Understanding them (really, deeply understanding them) will help you
   establish the mindset you need to write the rest of the code.
 *)

(* Sort a list by partitioning the list into elements larger
   and smaller then the head then sorting those partitions   *)
let rec sort = function
          | []      -> []
          | [x]     -> [x]
          | x :: xs -> let ys,zs = partition (x,xs,[],[])
                       in  List.append (sort ys) (x :: sort zs)
and partition = function
          | _,[],xs,ys      -> (xs,ys)
          | e,z :: zs,xs,ys -> if z < e
                                   then partition (e,zs,z :: xs,ys)
                                   else partition (e,zs,xs,z :: ys)


(* Apply a function to the second entry in a pair. *)
let second f (a, b) = (a, f b) 
let fst (a,_) = a
let snd (_,b) = b

(* Return list in which adjacent equal elements have been combined. *)
let rec unique = function
  | []         -> []
  | [x]        -> [x]
  | x::(y::ys) -> if x = y
                      then unique (y::ys)
                      else x :: unique (y::ys)

(* Sort and remove duplicates. *)
let uniqueSort xs = unique (sort xs);;

(* Return last element of list. *)
exception LastEmpty of string;;

let rec last = function
  | []    -> raise (LastEmpty "last given empty list.")
  | [x]   -> x
  | _::xs -> last xs

(* Return 'Some' last element of list or 'None'. *)
let rec safeLast = function
  | []    -> None
  | [x]   -> Some x
  | _::xs -> safeLast xs

(* Return 'Some' tail of a list or 'None'. *)
let safeTail = function
  | []    -> None
  | _::xs -> Some xs

(* Explode a string into a list of chars *)
let explode (s : string) : char list =
  let rec exp i l =
    if i < 0
      then l
      else exp (i-1) (s.[i] :: l)
  in  exp (String.length s - 1) []

(* Implode a list of chars into a string (due to OCaml's string
   representation this is not purely functional *)
let implode (l : char list) : string =
  let res = String.create (List.length l) in
  let rec imp i = function
    | [] -> res
    | c :: l -> res.[i] <- c; imp (i + 1) l 
  in  imp 0 l

(* Map a function over a list then concatenate the resulting lists. *)
let concatMap (f : 'a -> 'b list) (xs : 'a list) : 'b list = 
    List.fold_right (fun y ys -> List.append (f y) ys) xs []

(* Try to find the value associated with a given key in an
   association list. *)
let rec lookup (s : 'k) : ('k * 'v) list -> 'v option = function
  | [] -> None
  | (k,v) :: xs -> if k = s
                     then Some v
                     else lookup s xs

(* Map over an option if the value is a Some otherwise use the
   given default value. *)
let map_default (f : 'a -> 'b) (d : 'b) : 'a option -> 'b = function
  | Some v -> f v
  | None   -> d

(* Compute the or of a list. *)
let or_list xs = List.fold_right (||) xs false

(* Map a function taking three arguments across three lists where
   each list is supplying one of the arguments. 

     map3 f [a;...] [b;...] [c;...] === [f a b c;...]
   
   *)
let rec map3 f xs ys zs = match xs,ys,zs with
  | [],_ ,_
  | _ ,[],_
  | _ ,_ ,[]          -> []
  | x::xs,y::ys,z::zs -> f x y z :: map3 f xs ys zs




(* A 'Grammar' is a list of pairs of non-terminals and all their right-hand sides. *)
type grammar = (string * string list list) list

(* Return left-to-right fringe of tree as list. *)
let rec gflatten = function
  | [] -> []
  | (s,ps)::ss -> s :: List.append (List.concat ps) (gflatten ss);;

exception MissingStartSymbol of string;;

let startSymbol = function
  | ((s, _)::_) -> s
  | _           -> raise (MissingStartSymbol "Invalid grammar, no start symbol.");;

exception MissingEndMarker of string;;

let endMarker = function 
  | ((_, ps)::_) -> last (last ps)
  | _            -> raise (MissingEndMarker "Invalid grammar, no end marker.")

(* Return list of all nonterminals in grammar. *)
let nonterminals rs = List.map fst rs

(* Is s a nonterminal? *)
let isNonterminal s g = List.mem s (nonterminals g)

(* Return list of all symbols in grammar (no duplicates). *)
let gsymbols g = unique (sort (gflatten g))

(* Is s a symbol in grammar? *)
let isGSymbol s g = List.mem s (gsymbols g)

(* Return list of all terminals in grammar. *)
let terminals g = List.filter (fun x -> not (isNonterminal x g)) (gsymbols g)

(* Is s a terminal in grammar? *)
let isTerminal s g = isGSymbol s g && not (isNonterminal s g)

(* scanner: *)
let tokenize : string -> (string * string) list = fun program ->
    let get_id prog =
        let rec gi tok p =
            match p with
            | c :: rest when (('a' <= c && c <= 'z')
                           || ('A' <= c && c <= 'Z')
                           || ('0' <= c && c <= '9') || (c = '_'))
                -> gi (c :: tok) rest
            | _ -> (implode (List.rev tok), p) in
        gi [] prog in
    let get_int prog =
        let rec gi tok p =
            match p with
            | c :: rest when ('0' <= c && c <= '9')
                -> gi (c :: tok) rest
            | _ -> (implode (List.rev tok), p) in
        gi [] prog in
    let get_num prog =
        let (tok, rest) = get_int prog in
        match rest with
        | '.' :: c :: r when ('0' <= c && c <= '9')
            -> let (tok2, rest2) = get_int (c :: r) in
               ((tok ^ "." ^ tok2), rest2)
        | _ -> (tok, rest) in
    let rec get_error tok prog =
        match prog with
        | [] -> (implode (List.rev tok), prog)
        | c :: rest ->
            match c with
            | ':' | '+' | '-' | '*' | '/' | '(' | ')' | '[' | ']' | '_'
            | '<' | '>' | '=' | '!' | ',' | 'a'..'z' | 'A'..'Z' | '0'..'9'
                -> (implode (List.rev tok), prog)
            | _ -> get_error (c :: tok) rest in
    let rec skip_space prog =
        match prog with
        | [] -> []
        | c :: rest -> if c = ' ' || c = '\t' || c = '\n' || c = '\r'
                         then skip_space rest 
                         else prog in
    let rec tkize toks prog =
        match prog with
        | []                 -> (("$$" :: toks), [])
        | '\n' :: rest       -> tkize toks (skip_space prog)
        | '\r' :: rest       -> tkize toks (skip_space prog)
        | '\t' :: rest       -> tkize toks (skip_space prog)
        | ' ' :: rest        -> tkize toks (skip_space prog)
        | ':' :: '=' :: rest -> tkize (":=" :: toks) rest
        | ':' :: rest        -> tkize (":"  :: toks) rest
        | '+' :: rest        -> tkize ("+"  :: toks) rest
        | '-' :: rest        -> tkize ("-"  :: toks) rest
        | '*' :: rest        -> tkize ("*"  :: toks) rest
        | '/' :: rest        -> tkize ("/"  :: toks) rest
        | '(' :: rest        -> tkize ("("  :: toks) rest
        | ')' :: rest        -> tkize (")"  :: toks) rest
        | '[' :: rest        -> tkize ("["  :: toks) rest
        | ']' :: rest        -> tkize ("]"  :: toks) rest
        | '<' :: '=' :: rest -> tkize ("<=" :: toks) rest
        | '<' :: rest        -> tkize ("<"  :: toks) rest
        | '>' :: '=' :: rest -> tkize (">=" :: toks) rest
        | '>' :: rest        -> tkize (">"  :: toks) rest
        | '=' :: '=' :: rest -> tkize ("==" :: toks) rest
        | '!' :: '=' :: rest -> tkize ("!=" :: toks) rest
        | ',' :: rest        -> tkize (","  :: toks) rest
        | c   :: rest -> match c with
               | '0'..'9' -> let (t, rest) = get_num prog in
                             tkize (t :: toks) rest
               | 'a'..'z'
               | 'A'..'Z'
               | '_'      -> let (t, rest) = get_id prog in
                             tkize (t :: toks) rest
               | _        -> let (t, rest) = get_error [c] rest in
                             tkize (t :: toks) rest in
    let (toks, _) = (tkize [] (explode program)) in
    let categorize tok =
        match tok with
        | "array" | "begin" | "do"    | "else"  | "end"   | "float"
        | "for"   | "if"    | "int"   | "proc"  | "read"  | "real"
        | "then"  | "trunc" | "while" | "write"
        | ":=" | ":"  | "+"  | "-"  | "*"  | "/"  | "("
        | ")"  | "["  | "]"  | "<"  | "<=" | ">"  | ">="
        | "==" | "!=" | ","  | "$$"
            -> (tok, tok)
        | _ -> match tok.[0] with
               | '0'..'9' -> ("num", tok)
               | 'a'..'z'
               | 'A'..'Z' | '_' -> ("id", tok)
               | _ -> ("error", tok) in
    List.map categorize (List.rev toks);;

(* Returns true if the string is a number (this assumes
   that the value has already passed through the tokenizer). *)
let isTokNumber s =
  if String.length s = 0
    then false
    else match s.[0] with
           | '0'..'9' -> true
           | _        -> false

(* Return list of all productions in grammar.
   Each is represented as a (lhs, rhs) pair, where rhs is a list.
*)
let productions g = concatMap (fun (s,ps) -> List.map (fun p -> (s,p)) ps) g

(* Join lists together keeping only the unique elements. *)
let union xs = unique (sort (List.concat xs))

(* Return a list of pairs.
   Each pair consists of a symbol A and a list of symbols beta
   such that for some alpha, A -> alpha B beta.
*)
let rightContext (b : string) (g : grammar) : (string * string list) list =
  let rec h = function
    | s, []    -> None
    | s, p::ps -> if p = b then Some (s, ps) else h (s,ps)
  in concatMap (function
                | Some (s,ps) -> [(s,ps)]
                | _           -> []) 
               (List.map h (productions g))


  
(* ***************************************************
   Here is our good friend the calculator language,
   in the form expected by the parser generator.
   We've also provided the sum-and-average program
  
   Note that all symbols in the grammar are 'strings'.
  
*)
let calcGrammar : grammar =
    [ ("P",  [["SL"]])
    ; ("SL", [["S"; "SL"]; []])
    ; ("S",  [["id"; ":="; "E"]; ["read"; "id"]; ["write"; "E"]])
    ; ("E",  [["T"; "TT"]])
    ; ("T",  [["F"; "FT"]])
    ; ("TT", [["ao"; "T"; "TT"]; []])
    ; ("FT", [["mo"; "F"; "FT"]; []])
    ; ("ao", [["+"]; ["-"]])
    ; ("mo", [["*"]; ["/"]])
    ; ("F",  [["id"]; ["num"]; ["("; "E"; ")"]])
    ]

(* A program as a list of strings. *)
let sumAndAve = "
  read a
  read b
  sum := a + b
  write sum
  write sum / 2"

(* *********************************************************

   Here is the extended calculator grammar, with if and while statements.
   To demonstrate that the language is no longer a complete toy, we've
   provided a (rather slow) program to compute the first N prime numbers.

   Feel free to experiment with other grammars and inputs.

*)
let extendedCalcGrammar : grammar =
    [ ("P",  [["SL"]])
    ; ("SL", [["S"; "SL"]; []])
    ; ("S",  [ ["id"; ":="; "E"]; ["read"; "id"]; ["write"; "E"]
             ; ["if"; "C"; "SL"; "end"]; ["while"; "C"; "SL"; "end"]
             ])
    ; ("C",  [["E"; "rn"; "E"]])
    ; ("rn", [["=="]; ["!="]; ["<"]; [">"]; ["<="]; [">="]])
    ; ("E",  [["T"; "TT"]])
    ; ("T",  [["F"; "FT"]])
    ; ("TT", [["ao"; "T"; "TT"]; []])
    ; ("FT", [["mo"; "F"; "FT"]; []])
    ; ("ao", [["+"]; ["-"]])
    ; ("mo", [["*"]; ["/"]])
    ; ("F",  [["id"]; ["num"]; ["("; "E"; ")"]])
    ]

let primes = "read n
cp := 2
while n > 0
    found := 0
    cf1 := 2
    cf1s := cf1 * cf1
    while cf1s <= cp
        cf2 := 2
        pr := cf1 * cf2
        while pr <= cp
            if pr == cp
                found := 1
            end
            cf2 := cf2 + 1
            pr := cf1 * cf2
        end
        cf1 := cf1 + 1
        cf1s := cf1 * cf1
    end
    if found == 0
        write cp
        n := n - 1
    end
    cp := cp + 1
end" ;;

(* **************************************************************
 
   Next comes the parser generator.
   The main entry routine is 'makeParseTable', which takes a grammar as argument
   (in the format shown above) and returns an LL(1) parse table as a result.
   The table looks like the grammar, except that each RHS is replaced with a
   (predict-Set, RHS) pair.  The computational heart of the algorithm is the
   function getKnowledge.
 
   Much of the following employs a "Knowledge" data type.
   It's a list of "knowledgeEntry"s, one for each nonterminal,
   in the same order each nonterminal appears in the grammar
   (the order is important).
*)

type parseTable = (string * (string list * string list) list) list

type knowledgeEntry = 
  { nonterminal : string      (* Nonterminal A [not needed computationally,
                                 but included for readability of output]    *)
  ; epsilon     : bool        (* Do we currently think A can -->* epsilon   *)
  ; first       : string list (* (current guess at) FIRST(A)                *)
  ; follow      : string list (* (current guess at) Follow(A)               *)
  } ;;

type knowledge = (string * knowledgeEntry) list

(* Return knowledge structure with empty FIRST and FOLLOW sets
   and false gen-epsilon estimate for all symbols.
*)
let initialKnowledge (g : grammar) : knowledge = List.map
    (fun a -> (a,{nonterminal=a;epsilon=false;first=[];follow=[]}))
    (nonterminals g)

(* Return KnowledgeEntry for a given A. *)
let symbolKnowledge = lookup

(* Can w generate epsilon based on current estimates?
   if w is a terminal, no
   if w is a nonterminal, look it up
   if w is an empty list, yes
   if w is a non-empty list, "iterate" over elements
*)
let generatesEpsilon (w : string) (k : knowledge) (g : grammar) : bool = 
  if isTerminal w g
    then false
    else map_default (fun x -> x.epsilon) false (symbolKnowledge w k)

(* Return FIRST(w), based on current estimates.
   if w is a terminal, return (w)
   if w is a nonterminal, look it up
   if w is an empty list, return []  (empty set)
   if w is a non-empty list, "iterate" over elements
*)

let rec first (xs : string list) (k : knowledge) (g : grammar) : string list =
  let helper w = if isTerminal w g
                   then [w]
                   else map_default (fun x -> x.first) [] (symbolKnowledge w k)
  in  match xs with
        | []      -> []
        | w :: ws -> List.append (helper w) 
                                 (if generatesEpsilon w k g
                                    then first ws k g
                                    else [])

(* Return FOLLOW(A), based on current estimates. Simply look it up. *)
let follow a k = map_default (fun x -> x.follow) [] (symbolKnowledge a k)


(* Return knowledge structure for grammar.
   Start with 'initialKnowledge grammar' and "iterate",
   until the structure doesn't change.
   Uses 'rightContext b grammar', for all nonterminals 'b',
   to help compute follow sets.
*)
let getKnowledge g =
  let rcs = List.map (fun x -> rightContext x g) (nonterminals g) in
  let rec helper k = 
    let update (_, ke) (_, ps) cs = 
      let first' s  = first s k g in
      let gen    ss = List.for_all (fun s -> generatesEpsilon s k g) ss in
      let ff (s,w) = if gen w then follow s k else []
      in  (ke.nonterminal, 
             { ke with epsilon = ke.epsilon || or_list (List.map gen ps)
             ;         first   = union [ke.first; concatMap first' ps]
             ;         follow  = union [ke.follow; concatMap first' (List.map snd cs); concatMap ff cs]
             }) in
    let k' = map3 update k g rcs
    in if k = k' then k else helper k'
  in helper (initialKnowledge g)

(* Add a production to a grammar that includes an explicit end of file
   and wraps the original starting production. *)
let augmentWithStart (g : grammar) : grammar
  = match g with
      | []       -> []
      | (p,_)::_ -> ("$Start", [[p; "$$"]]) :: g

(* Return parse table for grammar. Uses the 'getKnowledge' function above. *)
let makeParseTable (g : grammar) : parseTable =
  let g' = augmentWithStart g in
  let k = getKnowledge g' in
  let h (l,rs) =
    let f r = (union [first r k g'
                     ; if List.for_all (fun r -> generatesEpsilon r k g') r
                         then follow l k 
                         else []
                     ], r)
    in  (l, List.map f rs) 
  in  List.map h g'

(* Double-index to find prediction (list of RHS symbols) for
   nonterminal nt and terminal t.
   Return 'Nothing' if not found.
*)
let parseLookup nt t table =
  let rec helper = function
    | [] -> None
    | (xs,ys)::ps -> if List.mem t xs 
                       then Some ys
                       else helper ps
  in  map_default helper None (lookup nt table)

(*
  
   The main parse routine below returns a parse tree as a 'Result' value
   (or an 'Error' error message if the program is syntactically invalid).
   To build that tree it employs a simplified version of the "attribute
   stack" described in Section 4.5.2 (pages 54-57) of the PLP CD.
  
   When it predicts A -> B C D, the parser pops A from the parse stack
   and then, before pushing D, C, and B (in that order), it pushes a
   number (in this case 3) indicating the length of the right hand side.
   It also pushes A into the attribute stack.
  
   When it matches a token, the parser pushes this into the attribute
   stack as well.
  
   Finally, when it encounters a number (say k) in the stack (as opposed
   to a character string), the parser pops k+1 symbols from the
   attribute stack, joins them together into a list, and pushes the list
   back into the attribute stack.
  
   These rules suffice to accumulate a complete parse tree into the
   attribute stack at the end of the parse.
  
   Note that everything is done functionally.  We don't really modify
   the stacks; we pass new versions to a tail recursive routine.
  
*)

(* Extract grammar from a 'parseTable', so we can invoke the various 
   routines that expect a grammar as argument.
*)
let toGrammar table = List.map (second (List.map snd)) table


(* A generic tree with n branches to hold the parse. *)
type 'a tree = Node of 'a * 'a forest
 and 'a forest = ('a tree) list

type parseTree = string tree
type attributeStack = string forest;;

(* Pop n + 1 symbols off the attribute stack,
   assemble into a production, and push back onto the stack.
*)
exception UnexpectedParseState of string;;

let reduceOneProd stack n =
  let rec h n ss ps = match n,ss,ps with
    | 0,_     ,Node (p,[])::ps -> Node (p, ps) :: ss
    | _,s::ss',ps              -> h (n-1) ss' (s::ps)
    | _,_     ,_               -> raise (UnexpectedParseState "Unexpected parse state in reduceOneProd.")
  in  h (1+n) stack []

(* Distinguish between numbers on the stack and symbols. *)
type parseStackEntry = PNum of int | PSym of string

type ('a,'b) either = Error of 'a | Result of 'b

(* To make the either type easier to work with we provide this helper
   function called bind (>>=) which allows you to compose values of the 
   either type with functions that my produce further values of the
   either type without first matching.  The behavior of bind is to 
   result in the first error or continue the computation while it is
   getting results.
*)
let ( >>= ) : ('e,'a) either -> ('a -> ('e,'b) either) -> ('e,'b) either
     = fun a f -> match a with
     | Error s  -> Error s
     | Result v -> f v

(* Unwraps the augmented parseTree to remove the added start root
   and explicit end of file $$ *)
let unwrap : parseTree -> (string, parseTree) either = function
  | Node ("$Start", [p; Node ("$$", [])]) -> Result p
  | _                                     -> Error ("expected parse wrapper")

(* Main parsing function. *)
let parse (table : parseTable) (p : string) : (string, parseTree) either =
  let g = toGrammar table in
  let die s = Error ("syntax error: " ^ s) in
  let rec helper ps ts ss = match (ps,ts,ss) with
    | []           ,[],a::_ -> Result a
    | []           ,_ ,_    -> die "extra input beyond end of program"
    | PNum n :: ps',_ ,_    -> (* We've reached the end of a production.  Pop lhs and rhs
                                  symbols off astack, join into list, and push back into astack. *)
                               helper ps' ts (reduceOneProd ss n)
    | _            ,[],_    -> die "unexpected end of program"
    | PSym t :: ps',((term,token)::ts'),_ -> 
        if isTerminal t g
          then (if t = term
                  then helper ps' ts' (Node (token,[]) :: ss) (* note push of token into astack *)
                  else die ("expected " ^ t ^ "; saw " ^ token))
          else match parseLookup t term table with
                 | Some rhs -> helper (List.append 
                                        (List.map (fun x -> PSym x) rhs) 
                                        (PNum (List.length rhs) :: ps'))
                                      ts
                                      (Node (t,[])::ss) (* note push of lhs into astack *)
                 | None     -> die ("no prediction for " ^ t ^ " when seeing " ^ token)
  in  helper [PSym (startSymbol g)] (tokenize p) [] >>= unwrap


(* **************************************************************
  
   Everything above this point in the file is complete and (I think)
   usable as-is.  The rest of the file, from here down, is a skeleton
   for the extra code you need to write.  It has been excised from my
   working solution to the assignment.  You are welcome, of course, to
   use a different organization if you prefer.  This is provided in the
   hope you may find it useful.
  
*)

exception Undefined of string;;
let undefined s _ = raise (Undefined ("There is still work to be done in "^s^"!"));;

(* First some types to represent the abstract syntax *)
type ast = statement list
 and ident = string
 and value = int
 and expr = Lit of value | Var of ident | Op of string * expr * expr
 and statement = Assign of ident * expr
               | Read of ident
               | Write of expr
               | If of cond * statement list
               | While of cond * statement list
 and cond = Cond of string * expr * expr;;

exception SyntaxError of string;;

(* You will need to write code to map from the `ParseTree`
   to the AST.  Where you see 'undefined' you will have
   to fill in with an actual implementation. *)
let rec toAstP : parseTree -> ast = undefined "toAstP"

(* Replace the 'something' with a pattern match which will bind the
   correct 's' and 'sl' so the RHS can be:  toAstS s :: toAstSL sl  *)
and toAstSL : parseTree -> ast = function
  | Node ("SL", something) -> undefined "toAstSL" () (* toAstS s :: toAstSL sl *)
  | _                      -> []

and toAstS : parseTree -> statement = function
(* Here you will want a pattern match on each LHS matching
   each RHS of the Statement data type (Assign, Read, ...). *)
  | _ -> undefined "toAstS" ()

and toAstC : parseTree -> cond = function
  | _ -> undefined "toAstC" ()

(* You can write 'toAstE' as a pair of functions.  The
   first handling the E, T, or F cases: *)
and toAstE : parseTree -> expr = function
(* First the base cases from 'F'
  | Node ("F", ...) -> ...
  | Node ("F", ...) -> ...
 then build terms or factors
  | Node (_, ...) -> toAstETail ... *)
  | _ -> undefined "toAstE" ()

(* The second function 'toAstETail' handles TT and FT *)
and toAstETail (e : expr) : parseTree -> expr = function
(* | Node (_, ...) -> ... (toAstE ...) ... *)
   | _ -> undefined "toAstETail" ()

(* ***************************************************** *)

(* Model the state of the calculator and track input and output *)
type environment =
  { values : (string * value) list
  ; input  : string list
  ; output : string list
  }

(* Memory *)

(* Be sure to understand this type!  Use 'Error' values to
   indicate errors. *)
let lookupEnv (n : string) (e : environment) : (string,value) either
  = undefined "lookupEnv" ()

let updateEnv (n : string) (e : environment) (v : value) : environment
  = undefined "updateEnv" ()

(* IO *)

let readEnv (e : environment) : (string,environment*value) either
  = undefined "readEnv" ()

let writeEnv (e : environment) (s : string) : environment
  = undefined "writeEnv" ()

(* ******************************************************* *)
(* The next two functions are complete and illustrate using
   the bind operator >>= to handle errors without our writing explicit
   matching for errors.*)
let rec interpret 
     (table   : parseTable)
     (program : string)
     (input   : string list)
              : (string,string list) either
  = parse table program >>= (fun t ->
      let ast = toAstP t
      in  interpretAst ast input)
(* equivalent with matching would be:
  = match parse table program with
      | Error s  -> Error s
      | Result t ->
      let ast = toAstP t
      in  interpretAst ast input
*)

and interpretAst (ast : ast) (input : string list) 
  = interpretSL ast {values=[]; input=input; output=[]} 
      >>= (fun e -> Result (List.rev e.output))
(* equivalent with matching would be:
  = match interpretSL ast {values=[]; input=input; output=[]} with
      | Error s  -> Error s
      | Result e -> Result (List.rev e.output) *)

and interpretSL : statement list -> environment -> (string,environment) either
  = undefined "interpretSL"

and interpretS (stmt : statement) (env : environment) : (string,environment) either
  = match stmt with
    | Assign (id, exp) ->
      Error "interpretS: Unimplemented Assign"
    | Read id ->
      (match env.input with
      | line :: rest ->
        let newEnv = updateEnv id env (int_of_string line) in
        Result {values=newEnv.values; input=rest; output=newEnv.output}
      | [] -> Error "Missing input to read")
    | Write exp ->
      interpretE exp env >>= (fun v ->
        let line = string_of_int v in
        Result {values=env.values; input=env.input; output=line :: env.output})
    | If (cnd, stmts) ->
      Error "interpretS: Unimplemented If"
    | While (cnd, stmts) ->
      Error "interpretS: Unimplemented While"

and interpretCond : cond -> environment -> (string,bool) either
  = undefined "interpretCond"

and interpretE : expr -> environment -> (string,value) either = function
  | Lit v -> fun env -> Result v
  | Var id -> fun env -> lookupEnv id env
  | Op (op, exp1, exp2) -> fun env ->
    interpretE exp1 env >>= (fun v1 ->
      interpretE exp2 env >>= (fun v2 ->
        match op with
        | "-" -> Result (v1 - v2)
        | "+" -> Result (v1 + v2)
        | "/" -> Result (v1 / v2)
        | "*" -> Result (v1 * v2)
        | _ -> Error ("Unknown operator "^op^"!")))


(* ****************************************************** *)

let rec interpret2
     (table   : parseTable)
     (program : string)
     (input   : string list)
              : (string,ast) either =
	      match parse table program with
	      | Result a -> Result (toAstP a)
	      | Error e  -> Error e

let rec print_parse_tree (t : (string,parseTree) either)  = match t with
	| Error e   -> print_string e 
	| Result Node(x,_) ->  print_string x
;;

let rec print_list (l : string list)  = function 
	| [] -> print_string ""
	| x::xt -> print_string x
;;

let sentence = "read a
read b
sum := a + b
write sum
write sum / 2";;

let tr = parse (makeParseTable extendedCalcGrammar) sentence;;

