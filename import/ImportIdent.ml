open Camlcoq

let intern_coqstring (cs : char list) : atom =
  intern_string (camlstring_of_coqstring cs)
