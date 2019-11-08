(**************************************
  Filename: Input.ml
  Project:  P3 Compilers
  Author:   Ling.Li
  Date:     2018.06.20
**************************************)

let read_channel channel = 
  let buf = Buffer.create 4096 in
  try 
    while true do
      let line = input_line channel in
      Buffer.add_string buf line;
      Buffer.add_char buf '\n'
    done;
    failwith "Input.read_channel: Out of infinite loop!"
  with
    End_of_file -> Buffer.contents buf
;;

let read_file filename =
  let in_channel = open_in filename in
  read_channel in_channel
;;