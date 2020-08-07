Require Import Ascii String BinNums.
Require Import ZArith.
Import BinNatDef.
Import BinIntDef.
Import BinPosDef.

Local Open Scope positive_scope.
Local Open Scope string_scope.

Module Binary.

Definition ascii_to_digit (ch : ascii) : option N
  := (if ascii_dec ch "0" then Some 0
      else if ascii_dec ch "1" then Some 1
      else None)%N.

Fixpoint pos_bin_app (p q:positive) : positive :=
  match q with
  | q~0 => (pos_bin_app p q)~0
  | q~1 => (pos_bin_app p q)~1
  | 1 => p~1
  end.

Module Raw.
  Fixpoint of_pos (p : positive) (rest : string) : string
    := match p with
       | 1 => String "1" rest
       | p'~0 => of_pos p' (String "0" rest)
       | p'~1 => of_pos p' (String "1" rest)
       end.

  Fixpoint to_N (s : string) (rest : N)
    : N
    := match s with
       | "" => rest
       | String ch s'
         => to_N
              s'
              match ascii_to_digit ch with
              | Some v => N.add v (N.double rest)
              | None => N0
              end
       end.

End Raw.

Definition of_pos (p : positive) : string
  := String "0" (String "b" (Raw.of_pos p "")).
Definition of_N (n : N) : string
  := match n with
     | N0 => "0b0"
     | Npos p => of_pos p
     end.
Definition of_Z (z : Z) : string
  := match z with
     | Zneg p => String "-" (of_pos p)
     | Z0 => "0b0"
     | Zpos p => of_pos p
     end.
Definition of_nat (n : nat) : string
  := of_N (N.of_nat n).

Definition to_N (s : string) : N
  := match s with
     | String s0 (String sb s)
       => if ascii_dec s0 "0"
          then if ascii_dec sb "b"
               then Raw.to_N s N0
               else N0
          else N0
     | _ => N0
     end.
Definition to_pos (s : string) : positive
  := match to_N s with
     | N0 => 1
     | Npos p => p
     end.
Definition to_Z (s : string) : Z
  := let '(is_neg, n) := match s with
                         | String s0 s'
                           => if ascii_dec s0 "-"
                              then (true, to_N s')
                              else (false, to_N s)
                         | EmptyString => (false, to_N s)
                         end in
     match n with
     | N0 => Z0
     | Npos p => if is_neg then Zneg p else Zpos p
     end.
Definition to_nat (s : string) : nat
  := N.to_nat (to_N s).

Fixpoint pos_neg_str (p : positive) (rest : string): string :=
  match p with
  | 1 => String "0" rest
  | p'~0 => pos_neg_str p' (String "1" rest)
  | p'~1 => pos_neg_str p' (String "0" rest)
  end.

Fixpoint add_head1 (num : nat) (rest : string) : string :=
  match num with
  | O => String "0" (String "b" rest)
  | S n' => add_head1 n' (String "1" rest)
  end.

Fixpoint add_head0 (num : nat) (rest : string) : string :=
  match num with
  | O => rest
  | S n' => add_head0 n' (String "0" rest)
  end.

Definition pos_neg (len : nat) (p : positive) : Z :=
  let p_str := pos_neg_str p "" in
  to_Z (add_head1 (len - length (p_str)) p_str).

Definition neg (len : nat) (n : Z) : Z :=
  match n with
  | Z0 => to_Z (add_head1 len "")
  | Zpos p => pos_neg len p
  | Zneg p => match pos_neg len p with
             | Zpos p' => Zneg p'
             | _ => Z0
             end
  end.

Fixpoint pos_or (a b : positive) : positive :=
  match a with
  | 1 => match b with
             | 1 => 1
             | b'~0 => b'~1
             | b'~1 => b'~1
        end
  | a'~0 => match b with
           | 1 => a'~1
           | b'~0 => (pos_or a' b')~0
           | b'~1 => (pos_or a' b')~1
           end
  | a'~1 => match b with
           | 1 => a'~1
           | b'~0 => (pos_or a' b')~1
           | b'~1 => (pos_or a' b')~1
           end
  end.

Definition or (a b : Z) : Z :=
  match a, b with
  | Z0, Zpos b' => b
  | Zpos a', Z0 => a
  | Z0, Z0 => Z0
  | Zpos a', Zpos b' => Zpos (pos_or a' b')
  | _ , _ => Z0  (* only support unsigned bits type *)
  end.

Fixpoint pos_and_raw (a b : string) : string :=
  match a, b with
  | "", "" => ""
  | String c1 r1, String c2 r2 => if ascii_dec c1 "0" then String "0" (pos_and_raw r1 r2)
                                 else String c2 (pos_and_raw r1 r2)
  | _, _ => "" (* exception*)
  end.
                                           
Definition pos_and (len : nat) (aa bb : string) : Z :=
  let a := match aa with
           | String "0" (String "b" rest) => rest
           | _ => "0"
           end in
  let b := match bb with
           | String "0" (String "b" rest) => rest
           | _ => "0"
           end in
  let sa := add_head0 (len - (length a)) a in
  let sb := add_head0 (len - (length b)) b in to_Z (String "0" (String "b" (pos_and_raw sa sb))).

Definition and (len : nat) (a b : Z) : Z :=
  match a, b with
  | Z0, _ => Z0
  | _, Z0 => Z0
  | Zpos a' , Zpos b' => pos_and len (of_pos a') (of_pos b')
  | _ , _ => Z0 (* only support unsigned bits type *)
  end.

Fixpoint pos_xor_raw (a b : string) : string :=
  match a, b with
  | "", "" => ""
  | String c1 r1, String c2 r2 => if ascii_dec c1 "0" then String c2 (pos_xor_raw r1 r2)
                                 else if ascii_dec c2 "0" then String "1" (pos_xor_raw r1 r2)
                                      else String "0" (pos_xor_raw r1 r2)
  | _ , _ => "" (* excepretion *)
  end.

Definition pos_xor (len : nat) (aa bb : string) : Z :=
  let a := match aa with
           | String "0" (String "b" rest) => rest
           | _ => "0"
           end in
  let b := match bb with
           | String "0" (String "b" rest) => rest
           | _ => "0"
           end in
  let sa := add_head0 (len - (length a)) a in
  let sb := add_head0 (len - (length b)) b in to_Z (String "0" (String "b" (pos_xor_raw sa sb))).

Definition xor (len : nat) (a b : Z) : Z :=
  match a, b with
  | Z0, _ => b
  | _, Z0 => a
  | Zpos a' , Zpos b' => pos_xor len (of_pos a') (of_pos b')
  | _ , _ => Z0 (* only support unsigned bits type *)
  end.

Definition bc (len1 len2 : nat) (a b : Z) : Z :=
  match a, b with
  | Zneg p, _ => Z0 (* exception *)
  | _, Zneg p => Z0 (* exception *)
  | _, _ => Z.add (Z.mul a (Zpower_nat 2 len2)) b
  end.

End Binary.

Module Hex.

Definition ascii_to_digit (ch : ascii) : option N
  := (if ascii_dec ch "0" then Some 0
      else if ascii_dec ch "1" then Some 1
      else if ascii_dec ch "2" then Some 2
      else if ascii_dec ch "3" then Some 3
      else if ascii_dec ch "4" then Some 4
      else if ascii_dec ch "5" then Some 5
      else if ascii_dec ch "6" then Some 6
      else if ascii_dec ch "7" then Some 7
      else if ascii_dec ch "8" then Some 8
      else if ascii_dec ch "9" then Some 9
      else if ascii_dec ch "a" then Some 10
      else if ascii_dec ch "A" then Some 10
      else if ascii_dec ch "b" then Some 11
      else if ascii_dec ch "B" then Some 11
      else if ascii_dec ch "c" then Some 12
      else if ascii_dec ch "C" then Some 12
      else if ascii_dec ch "d" then Some 13
      else if ascii_dec ch "D" then Some 13
      else if ascii_dec ch "e" then Some 14
      else if ascii_dec ch "E" then Some 14
      else if ascii_dec ch "f" then Some 15
      else if ascii_dec ch "F" then Some 15
      else None)%N.

Fixpoint pos_hex_app (p q:positive) : positive :=
  match q with
  | 1 => p~0~0~0~1
  | 2 => p~0~0~1~0
  | 3 => p~0~0~1~1
  | 4 => p~0~1~0~0
  | 5 => p~0~1~0~1
  | 6 => p~0~1~1~0
  | 7 => p~0~1~1~1
  | 8 => p~1~0~0~0
  | 9 => p~1~0~0~1
  | 10 => p~1~0~1~0
  | 11 => p~1~0~1~1
  | 12 => p~1~1~0~0
  | 13 => p~1~1~0~1
  | 14 => p~1~1~1~0
  | 15 => p~1~1~1~1
  | q~0~0~0~0 => (pos_hex_app p q)~0~0~0~0
  | q~0~0~0~1 => (pos_hex_app p q)~0~0~0~1
  | q~0~0~1~0 => (pos_hex_app p q)~0~0~1~0
  | q~0~0~1~1 => (pos_hex_app p q)~0~0~1~1
  | q~0~1~0~0 => (pos_hex_app p q)~0~1~0~0
  | q~0~1~0~1 => (pos_hex_app p q)~0~1~0~1
  | q~0~1~1~0 => (pos_hex_app p q)~0~1~1~0
  | q~0~1~1~1 => (pos_hex_app p q)~0~1~1~1
  | q~1~0~0~0 => (pos_hex_app p q)~1~0~0~0
  | q~1~0~0~1 => (pos_hex_app p q)~1~0~0~1
  | q~1~0~1~0 => (pos_hex_app p q)~1~0~1~0
  | q~1~0~1~1 => (pos_hex_app p q)~1~0~1~1
  | q~1~1~0~0 => (pos_hex_app p q)~1~1~0~0
  | q~1~1~0~1 => (pos_hex_app p q)~1~1~0~1
  | q~1~1~1~0 => (pos_hex_app p q)~1~1~1~0
  | q~1~1~1~1 => (pos_hex_app p q)~1~1~1~1
  end.

Module Raw.
  Fixpoint of_pos (p : positive) (rest : string) : string
    := match p with
       | 1 => String "1" rest
       | 2 => String "2" rest
       | 3 => String "3" rest
       | 4 => String "4" rest
       | 5 => String "5" rest
       | 6 => String "6" rest
       | 7 => String "7" rest
       | 8 => String "8" rest
       | 9 => String "9" rest
       | 10 => String "a" rest
       | 11 => String "b" rest
       | 12 => String "c" rest
       | 13 => String "d" rest
       | 14 => String "e" rest
       | 15 => String "f" rest
       | p'~0~0~0~0 => of_pos p' (String "0" rest)
       | p'~0~0~0~1 => of_pos p' (String "1" rest)
       | p'~0~0~1~0 => of_pos p' (String "2" rest)
       | p'~0~0~1~1 => of_pos p' (String "3" rest)
       | p'~0~1~0~0 => of_pos p' (String "4" rest)
       | p'~0~1~0~1 => of_pos p' (String "5" rest)
       | p'~0~1~1~0 => of_pos p' (String "6" rest)
       | p'~0~1~1~1 => of_pos p' (String "7" rest)
       | p'~1~0~0~0 => of_pos p' (String "8" rest)
       | p'~1~0~0~1 => of_pos p' (String "9" rest)
       | p'~1~0~1~0 => of_pos p' (String "a" rest)
       | p'~1~0~1~1 => of_pos p' (String "b" rest)
       | p'~1~1~0~0 => of_pos p' (String "c" rest)
       | p'~1~1~0~1 => of_pos p' (String "d" rest)
       | p'~1~1~1~0 => of_pos p' (String "e" rest)
       | p'~1~1~1~1 => of_pos p' (String "f" rest)
       end.

  Fixpoint to_N (s : string) (rest : N)
    : N
    := match s with
       | "" => rest
       | String ch s'
         => to_N
              s'
              match ascii_to_digit ch with
              | Some v => N.add v (N.mul 16 rest)
              | None => N0
              end
       end.

End Raw.

Definition of_pos (p : positive) : string
  := String "0" (String "x" (Raw.of_pos p "")).
Definition of_N (n : N) : string
  := match n with
     | N0 => "0x0"
     | Npos p => of_pos p
     end.
Definition of_Z (z : Z) : string
  := match z with
     | Zneg p => String "-" (of_pos p)
     | Z0 => "0x0"
     | Zpos p => of_pos p
     end.
Definition of_nat (n : nat) : string
  := of_N (N.of_nat n).

Definition to_N (s : string) : N
  := match s with
     | String s0 (String so s)
       => if ascii_dec s0 "0"
          then if ascii_dec so "x"
               then Raw.to_N s N0
               else N0
          else N0
     | _ => N0
     end.
Definition to_pos (s : string) : positive
  := match to_N s with
     | N0 => 1
     | Npos p => p
     end.
Definition to_Z (s : string) : Z
  := let '(is_neg, n) := match s with
                         | String s0 s'
                           => if ascii_dec s0 "-"
                              then (true, to_N s')
                              else (false, to_N s)
                         | EmptyString => (false, to_N s)
                         end in
     match n with
     | N0 => Z0
     | Npos p => if is_neg then Zneg p else Zpos p
     end.
Definition to_nat (s : string) : nat
  := N.to_nat (to_N s).

Definition bc (len1 len2 : nat) (a b : Z) : Z :=
  match a, b with
  | Zneg p, _ => Z0 (* exception *)
  | _, Zneg p => Z0 (* exception *)
  | _, _ => Z.add (Z.mul a (Zpower_nat 16 len2)) b
  end.

End Hex.

Module Decimal.
Definition ascii_to_digit (ch : ascii) : option N
  := (if ascii_dec ch "0" then Some 0
      else if ascii_dec ch "1" then Some 1
      else if ascii_dec ch "2" then Some 2
      else if ascii_dec ch "3" then Some 3
      else if ascii_dec ch "4" then Some 4
      else if ascii_dec ch "5" then Some 5
      else if ascii_dec ch "6" then Some 6
      else if ascii_dec ch "7" then Some 7
      else if ascii_dec ch "8" then Some 8
      else if ascii_dec ch "9" then Some 9
      else None)%N.

Module Raw.

  Fixpoint to_N (s : string) (rest : N)
    : N
    := match s with
       | "" => rest
       | String ch s'
         => to_N
              s'
              match ascii_to_digit ch with
              | Some v => N.add v (N.mul 10 rest)
              | None => N0
              end
       end.

End Raw.

Definition to_N (s : string) : N
  := Raw.to_N s N0.
     
Definition to_pos (s : string) : positive
  := match to_N s with
     | N0 => 1
     | Npos p => p
     end.
Definition to_Z (s : string) : Z
  := let '(is_neg, n) := match s with
                         | String s0 s'
                           => if ascii_dec s0 "-"
                              then (true, to_N s')
                              else (false, to_N s)
                         | EmptyString => (false, to_N s)
                         end in
     match n with
     | N0 => Z0
     | Npos p => if is_neg then Zneg p else Zpos p
     end.
Definition to_nat (s : string) : nat
  := N.to_nat (to_N s).

End Decimal.

Fixpoint length_of_P (p : positive) : nat
  := match p with
     | 1 => 1%nat
     | p'~0 => S (length_of_P p')
     | p'~1 => S (length_of_P p')
     end.

Definition length_of_Z (z : Z) : nat
  := match z with
     | Zneg p => length_of_P p
     | Z0 => 1%nat
     | Zpos p => length_of_P p
     end.
