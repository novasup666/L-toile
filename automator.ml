open Format

type letter = char
type word = letter list
type language = word list
type state = int
type fa = {nb_etats: int; transis : ((letter*state) list) array; initial: state; finaux : bool array}


let noux a b =
  (*Non ou exclusif,n'est vrai que lorque a et b sont dans le même état (les deux vrai ou les deux faux)*)
  not((a || b) && not (a && b));;

(* A generic pretty-printer for words *)
let pp_word fmt (w: word) = match w with
  | [] -> fprintf fmt "ε"
  | _ -> let pp_sep fmt () = fprintf fmt "" in
  pp_print_list ~pp_sep pp_print_char fmt w


(* A pretty-printer for words in standard output *)
let print_word (w: word) =
  fprintf std_formatter "%a" pp_word w


(* make_t_equiv oracle t returns a function computing T-equivalence
that uses oracle to know whether a word should be recognized *)
let make_t_equiv (oracle: word -> bool) (t: language) :( word * word) -> bool =
  let res (w1,w2) = 
    let rec inner t =
      match t with
      |[] -> true
      |v::vs ->  (noux (oracle (w1@v)) (oracle (w2@v))) && (inner vs) 
    in
    inner t

  in
  res 




let memo f = 
  let dico =  Hashtbl.create 20 in
  fun x -> match Hashtbl.find_opt dico x with
            |None -> let y = f x in Hashtbl.add dico x y; y
            |Some y -> y

(* ask_in w asks the user whether word w should be recognized and returns
the answer *)
let rec ask_in (w: word) : bool =
  printf "Est-ce que le mot:\n";
  print_word w;
  printf "\nest reconnu ? [o/n]";
  print_newline ();
  match (input_line stdin) with
    | "o" -> true
    | "n" -> false
    | _ -> printf "Répondre par o ou n\n"; ask_in w


(* is_init a q returns true if q is an initial state of a, false otherwise *)
let is_init (a: fa) (q: state) : bool =
  (a.initial = q)


(* is_final a q returns true if q is a final state of a, false otherwise *)
let is_final (a: fa) (q: state) : bool = a.finaux.(q) 


(* iter_states f a applies function f to every state of a *)
let iter_states (f: state -> unit) (a: fa) : unit =
  for i = 0 to (a.nb_etats - 1) do 
    f i
  done
    


(* iter_trans f a applies function f to every transition of a *)
let iter_trans (f: state -> letter -> state -> unit) (a: fa) : unit =
  let n =  a.nb_etats in
  for i=0 to n-1 do
    List.iter (fun (l,s) -> f i l s) (a.transis.(i))
  done

(* display name a creates files name.dot and name.svg representing a *)
let display (name: string) (a: fa) : unit =
  let oc = open_out (name ^ ".dot") in
  let f = formatter_of_out_channel oc in
  fprintf f "digraph g {\n";
  iter_states (
    fun q ->
      if is_final a q then
        fprintf f "  %d [shape=doublecircle];\n" q
      else
        fprintf f "  %d [shape=circle];\n" q;
      if is_init a q then (
        fprintf f "  i%d [style=invis];\n" q;
        fprintf f "  i%d -> %d;\n" q q)
  ) a;
  iter_trans (fun q l q2 -> fprintf f "  %d -> %d [label=%c]\n" q q2 l) a;
  fprintf f "}\n";
  close_out oc;
  let _ = Sys.command (sprintf "dot -Tsvg -o %s.svg %s.dot" name name) in ()


(* ask_equiv a asks the user whether automaton a is equivalent to the hidden
automaton and returns the answer *)
let rec ask_equiv (a: fa) : bool =
  display "essai" a;
  printf "Est-ce que l’automate \"essai\" est la solution ? [o/n]";
  print_newline ();
  match (input_line stdin) with
    | "o" -> true
    | "n" -> false
    | _ -> printf "Répondre par o ou n\n"; ask_equiv a
  



(* guess oracle sigma s t returns the automaton associated with S and T
and based on oracle *)
let guess (oracle: word -> bool) (sigma: letter list) (s: language) (t: language) : fa =
  let n = List.length s in
  let finaux = Array.make n false in
  let sont_tequiv = make_t_equiv oracle t in
  let transi = Array.make n ([]) in
  let rec compute_finaux s i = 
    match s with
    | [] -> ()
    |x::xs-> finaux.(i) <- oracle(x); compute_finaux xs (i+1)
  in
  compute_finaux s 0;
  let rec compute_transi l i =
    match l with
    | [] -> ()
    |x::xs ->( 
      let rec inner s j = 
        match s with
        | [] -> ()
        | y::ys -> (List.iter (fun c ->(if sont_tequiv (x@[c],y) 
                                        then transi.(i) <- (c,j)::(transi.(i))
                                        )
                              ) 
                              sigma);
                    inner ys (j+1)
      in
      inner s 0;
      compute_transi xs (i+1)
      )
  in
  compute_transi s 0;
  let rec compute_initial s i = 
    match s with
    | [] -> failwith "Il n'y à pas epsilon dans S"
    | x::xs -> if x=[] then i else compute_initial xs (i+1)
  in
  let initial = compute_initial s 0 in
  let fa = {nb_etats = n;
        transis = transi;
        initial = initial;
        finaux = finaux
        }
  in
  fa
 
let rec pp_l l = 
  match l with
  |[] -> ()
  |w::ws -> print_word w;
            printf " ";
             pp_l ws
  
  (* Given (S, T) a correct pair, extend_s oracle sigma s t returns S' an
extension of S such that (S', T) is correct and complete, based on oracle *)
let extend_s (oracle: word -> bool) (sigma: letter list) (s: language) (t: language) : language =
  let sont_tequiv = make_t_equiv oracle t in
  let rec new_from_u s u sigma res = 
    match sigma with
    | [] -> res
    | x::xs ->  let new_word = u@[x] in
                let rec is_u_really_new s =(
                  match s with
                  | [] -> true
                  | u::us -> (not (sont_tequiv (new_word,u))) && is_u_really_new us)
                in
                if is_u_really_new s then new_from_u (new_word::s) u xs  (new_word::res) 
                else new_from_u s u xs res
  in
  let rec iter to_try new_s=
    match to_try with
    |[] -> new_s
    |u::us -> (let new_words = new_from_u new_s u sigma [] in 
              iter (new_words@us) (new_s@new_words))
  in

  iter s s
  
(* extend_t t w returns a new language that is the union of t
and every suffix of w *)
let extend_t (t: language) (w: word) : language =
  let rec compute_suffixes w = 
    match w with
    |[] -> []
    |c::cs -> w::(compute_suffixes cs)
  in
  (compute_suffixes w)@t


(* Lets the user provide the alphabet sigma *)
let get_sigma () : letter list =
  printf "Donnez l’alphabet en séparant les lettres par \',\' (sans espaces)";
  print_newline ();
  let sigma = input_line stdin in
  let sigma = String.split_on_char ',' sigma in
  List.map (fun l -> l.[0]) sigma


let string_to_char_list s = List.init (String.length s) (String.get s) 

(* l_star () plays a game of automaton guessing *)
let l_star () =
  let s = [[]] in
  let t = [[]] in
  let sigma = get_sigma () in
  let oracl = memo ask_in in
  let rec inner s t  = 
    let a = guess oracl sigma s t in
    display "avtomat" a;
    if ask_equiv a then a else (
      printf "Entrez un contre-exemple";
      print_newline ();
      let nw_string = input_line stdin in
      let nw = string_to_char_list nw_string in
      let nt = extend_t t nw in
      let ns = extend_s oracl sigma s nt in

      inner ns nt
    ) 
  in
  let fa = inner s t in
  printf "L'automate se trouve dans le fichier avtomat !";
  print_newline ();
  display "avtomat" fa



let _ = l_star ()