type letter = char
type word = letter list
type language = word list
type state = int
type fa = {nb_etats: int; 
            transis : ((letter*state) list) array; 
            initial: state; 
            finaux : bool array}


(* make_t_equiv oracle t returns a function computing T-equivalence
that uses oracle to know whether a word should be recognized *)
val make_t_equiv : (word -> bool) -> language -> (word * word -> bool)

(* A generic pretty-printer for words *)
val pp_word : Format.formatter -> word -> unit

(* A pretty-printer for words in standard output *)
val print_word : word -> unit

(* ask_in w asks the user whether word w should be recognized and returns
the answer *)
val ask_in : word -> bool

(* is_init a q returns true if q is an initial state of a, false otherwise *)
val is_init : fa -> state -> bool

(* is_final a q returns true if q is a final state of a, false otherwise *)
val is_final : fa -> state -> bool

(* iter_states f a applies function f to every state of a *)
val iter_states : (state -> unit) -> fa -> unit

(* iter_trans f a applies function f to every transition of a *)
val iter_trans : (state -> letter -> state -> unit) -> fa -> unit

(* display name a creates files name.dot and name.svg representing a *)
val display : string -> fa -> unit

(* ask_equiv a asks the user whether automaton a is equivalent to the hidden
automaton and returns the answer *)
val ask_equiv : fa -> bool

(* guess oracle sigma s t returns the automaton associated with S and T
and based on oracle *)
val guess : (word -> bool) -> letter list -> language -> language -> fa

(* Given (S, T) a correct pair, extend_s oracle sigma s t returns S' an
extension of S such that (S', T) is correct and complete, based on oracle *)
val extend_s : (word -> bool) -> letter list -> language -> language -> language

(* extend_t t w returns a new language that is the union of t
and every suffix of w *)
val extend_t : language -> word -> language

(* Lets the user provide the alphabet sigma *)
val get_sigma : unit -> letter list

(* l_star () plays a game of automaton guessing *)
val l_star : unit -> unit
