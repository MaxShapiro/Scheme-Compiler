module Labels : sig
  val make_label : string -> string
  val make_labels : string list -> string list
end = struct
  let label_counter = ref 0;;
    
  let count () =
    ( label_counter := 1 + !label_counter ;
      !label_counter );;
    
  let make_label base =
    Printf.sprintf "%s_%d" base (count());;
    
  let make_labels bases =
    let n = count() in
    List.map (fun base -> Printf.sprintf "%s_%d" base n)
	     bases;;
end;;
  
