
(* Concatenates a list of strings. *)
fun catstrings [] = ""
  | catstrings (a::rest) = a ^ catstrings rest;

(* Removes elements of list if the predicate on an element is true. *)
fun filter p [] = []
 |  filter p (a::rest) = if p a then filter p rest else a::filter p rest;

(* Removes duplicates from a list determined by function f. *)
fun removedups _ [] = []
  | removedups f (a::rest) = a::removedups f (filter (fn x=> f(a, x)) rest);

(* Reduces a list lists by one dimension. *)
fun flatten [] = []
  | flatten (a::rest) = a @ flatten rest;

(* Converts digit char to digit int. *)
fun char2int c = ord c - ord #"0";

(* Converts char list to int list. *)
fun cl2il lst = map char2int lst;

(* Converts digit int to digit char. *)
fun int2char i = chr (i + ord #"0");

(* Converts int list to char list. *)
fun dl2cl lst = map int2char lst;

(* Converts int to String. *)
fun inttostring 0 = "0"
  | inttostring i =
    let fun helper 0 = [] |
          helper i = helper (i div 10) @ [int2char (i mod 10)]
    in if i < 0 then implode (#"~"::(helper (abs i))) else implode(helper i) end;

(* Generates a list [f(0), f(1), .. , f(n-1)]. *)
fun tabulate _ 0 = []
  | tabulate f n = (tabulate f (n - 1)) @ [(f (n - 1))];

exception InvalidIndex;
(* Inserts value a into a list at position i.
   Raises Invalid Index if index is invalid. *)
fun insert (a, 0, lst) = a::lst
  | insert (_, _, []) = raise InvalidIndex
  | insert (a, i, b::rest) = b::insert (a, i - 1, rest);

(* Inserts a into all places in a list. *)
fun allplaces a lst = tabulate (fn x => insert (a, x, lst)) (length lst + 1);

(* Generates all permutations of a list. *)
fun perms [] = [[]]
  | perms (a::rest) = flatten (map (fn x => allplaces a x) (perms rest));

(*------------ BIG INT ------------*)

exception InvalidBigInt;

(* Datatype declaration for bigint. *)
datatype bigint = BIG of string;

(* Returns boolean true if char is a digit. *)
fun isdigit #"0" = true
| isdigit #"1" = true
| isdigit #"2" = true
| isdigit #"3" = true
| isdigit #"4" = true
| isdigit #"5" = true
| isdigit #"6" = true
| isdigit #"7" = true
| isdigit #"8" = true
| isdigit #"9" = true
| isdigit _ = false;

(* Returns true if all elements of a list evaluate
   to true based on a given predicate. *)
fun all _ [] = true
  | all pred (a::rest) = pred a andalso all pred rest;

(* Returns true if all elements of a char list are digits *)
fun alldigits lst = all isdigit lst;

(* Converts String to bigint.
   Raises InvalidBigInt if invalid String. *)
fun makebigint str =
  let fun helper [] = false
    | helper (#"0"::rest) = if not (null rest) then false else true
    | helper (#"~"::[]) = raise InvalidBigInt
    | helper (#"~"::rest) = if (hd rest) = #"0" then raise InvalidBigInt else helper rest
    | helper lst = alldigits lst
  in if helper (explode str) then BIG str else raise InvalidBigInt end;

(* Constructs bigint from String.
   Adjusts string to construct valid bigint. *)
fun constructbigint lst =
  let fun helper [] = ""
    | helper [#"0"] = "0"
    | helper (#"0"::rest) = helper rest
    | helper [#"~", #"0"] = "0"
    | helper (#"~"::rest) =
      let val other = helper rest
      in if other = "0" then "0" else "~" ^ helper rest end
    | helper lst = implode lst
  in BIG (helper lst) end;

(* Compare function for bigints. *)
fun compare ((BIG str1), (BIG str2)) =
  let fun helper ([], []) = EQUAL
    | helper ([], _) = LESS
    | helper (_, []) = GREATER
    | helper ((#"~"::rest1), (#"~"::rest2)) = helper(rest2, rest1)
    | helper ((#"~"::_), _) = LESS
    | helper (_, (#"~"::_)) = GREATER
    | helper ((a::resta), (b::restb)) =
        if (length (a::resta)) > (length (b::restb)) then GREATER
        else if (length (a::resta)) < (length (b::restb)) then LESS
        else if a = b then helper (resta, restb)
        else if (char2int a) > (char2int b) then GREATER
        else LESS;
   in helper ((explode str1), (explode str2)) end;

fun dec_add(v1, v2, carry) =
 let val sum = v1 + v2 + carry
  in (sum mod 10, sum div 10) end;

fun big_add_helper (0, [], []) = []
 | big_add_helper (1, [], []) = [1]
 | big_add_helper (c, [], list) = big_add_helper (c, [0], list)
 | big_add_helper (c, list, []) = big_add_helper (c, list, [0])
 | big_add_helper (c, a::resta, b::restb) =
    let val (result, carry) = dec_add(a, b, c)
     in result::big_add_helper (carry, resta, restb) end;

fun dec_sub(v1, v2, borrow) =
 let val sum = v1 - v2 - borrow
  in if sum < 0 then (sum + 10, 1) else (sum, 0) end;

exception Neg;

fun big_sub_helper(0, [], []) = []
| big_sub_helper(1, [], []) = raise Neg
| big_sub_helper(b, [], list) = big_sub_helper(b, [0], list)
| big_sub_helper(b, list, []) = big_sub_helper(b, list, [0])
| big_sub_helper(b, x::restx, y::resty) =
  let val (result, borrow) = dec_sub(x,y,b)
   in result::big_sub_helper (borrow, restx, resty) end;

(* Helper for calling big_sub_helper and big_add_helper. *)
fun call_helper helper (lst1, lst2) =
 dl2cl (rev (helper (0, (rev (cl2il lst1)), (rev (cl2il lst2)))));

fun dec_mul (v1, v2, carry) =
  let val quot = (v1 * v2) + carry
  in (quot mod 10, quot div 10) end;

(* Multiplies an int list by an int. *)
fun big_mul_helper (0, [], _) = []
  | big_mul_helper (c, [], _) = [c]
  | big_mul_helper (c, x::rest, i) =
    let val (result, carry) = dec_mul (x, i, c)
    in result::big_mul_helper (carry, rest, i) end;

(* Helper for calling big_mul_helper. *)
fun call_mul_helper (lst, c) =
  dl2cl (rev (big_mul_helper (0, (rev (cl2il lst)), (char2int c))));

(* Function to perform arithmetic addition on char lists. *)
fun addition ((#"~"::rest1), (#"~"::rest2)) = #"~"::(call_helper big_add_helper (rest1, rest2))
  | addition ((#"~"::rest1), lst2) = if (compare ((BIG (implode rest1)), (BIG (implode lst2)))) = GREATER
                                  then #"~"::call_helper big_sub_helper (rest1, lst2)
                                  else call_helper big_sub_helper (lst2, rest1)
  | addition (lst1, (#"~"::rest2)) = if (compare ((BIG (implode lst1)), (BIG (implode rest2)))) = GREATER
                                  then call_helper big_sub_helper (lst1, rest2)
                                  else #"~"::call_helper big_sub_helper (rest2, lst1)
  | addition (lst1 , lst2) = call_helper big_add_helper (lst1, lst2);

(* Adds bigints *)
fun add ((BIG s), (BIG t)) = constructbigint (addition ((explode s), (explode t)));

(* Subtracts bigints. *)
fun sub ((BIG strint1), (BIG strint2)) =
  let val lst1 = explode strint1
      val lst2 = explode strint2
  in if (hd lst2) = #"~" then constructbigint (addition (lst1, (tl lst2)))
     else constructbigint (addition (lst1, (#"~"::lst2))) end;

(* Performs multiplication on char lists. *)
fun multiplier (_, []) = []
  | multiplier (lst, a::rest) = addition ((call_mul_helper (lst, a)), (multiplier (lst, rest)) @ [#"0"]);

(* Performs multiplication on bigints. *)
fun mul ((BIG s), (BIG t)) =
  let fun helper ((#"~"::resta), (#"~"::restb)) = multiplier (resta, (rev restb))
    | helper ((#"~"::resta), (lstb)) = #"~"::multiplier (resta, (rev lstb))
    | helper (lsta, (#"~"::restb)) = #"~"::multiplier (lsta, (rev restb))
    | helper (lsta, lstb) = multiplier (lsta, (rev lstb))
  in constructbigint (helper ((explode s), (explode t))) end;

(* Splits char lists of digits into two equal halfs. *)
fun split_helper ([], _) = ([], [])
  | split_helper ((a::[]), carry) = ([(a + carry) div 2], [((a + carry) div 2) + ((a + carry) mod 2)])
  | split_helper ((a::rest), carry) =
    let val b = (a + carry) div 2
        val (r1, r2) = split_helper (rest, ((a + carry) mod 2 * 10))
    in (b::r1, b::r2) end;

(* Splits bigint into two halfs and returns two bigints. *)
fun split (BIG s) =
  let val (s1, s2) = split_helper((cl2il (explode s)), 0)
  in (constructbigint (dl2cl s1), constructbigint (dl2cl s2)) end;

(* Bigint to the power of a non-negative bigint .*)
fun pow (_, BIG "0") = (BIG "1")
  | pow (s, BIG "1") = s
  | pow (s, BIG t) =
    let val (BIG t1, BIG t2) = split (BIG t)
    in mul (pow (s, BIG t1), pow (s, BIG t2)) end;
