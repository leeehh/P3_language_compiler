let output_path filename =
  let basename = Filename.basename (Filename.chop_extension filename) in
  let dirname = Filename.dirname filename in
  let filepath =
    if !output_file = "" then (Filename.concat dirname basename)
    else if (Filename.is_implicit !output_file) then (Filename.concat !dirname !output_file)
    else !output_file in
  Filename.chop_extension filepath
;;
