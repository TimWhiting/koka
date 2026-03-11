def f (s : String) :=
  let parts := s.split (fun c => c == ',' || c == ';')
  List.foldl (fun (acc : Nat) (part : String) => acc + part.length) 0 parts
