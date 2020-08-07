Require Import Coqlib Errors.
Require Import BinNums NPeano.
Require Import String.
Require Import Types.
Require Import Tree.
Require Import StringtoInt.

Local Open Scope string_scope.

(* full version with TConst Constructor*)
Definition typecheck_constant (envs : id_scope) (c : constant) : res ty :=
  match c with
  | Const_Identifier id => find_scope_id id envs
  | Const_Int x => OK (TConst TInt (StringtoInt.Decimal.to_Z (get_idname x)))
  | Const_Hex x => OK (TConst (THexes (pred (pred (length (get_idname x))))) (StringtoInt.Hex.to_Z (get_idname x)))
  | Const_Bit x => OK (TConst (TBits (length (get_idname x))) (StringtoInt.Binary.to_Z (get_idname x)))
  end.

(* Test constant *)
(*
Check typecheck_constant.
Check "123".

Compute typecheck_constant empty_id_env (Const_Int {| name:="-1234"; key:=3 |}).
Compute typecheck_constant empty_id_env (Const_Hex {| name:="-0x123afe"; key:=4 |}).
Compute typecheck_constant empty_id_env (Const_Bit {| name:="-0b101010101"; key:=5 |}).
Compute typecheck_constant (("id1",TConst TInt 5)::nil) (Const_Identifier {| name:="id1"; key:=6 |}).
 *)

(*only constexpr?*)
Definition typecheck_unary (u : unary_operator) (oty : res ty) :=
  match oty with
  | Error e => Error e
  | OK ty =>
               match u, ty with
               | Unary_Int, (TConst t val) => OK (TConst TInt val)
               | Unary_Not, TBool => OK TBool
               | Unary_Tilde, (TConst (TBits x) val) => OK (TConst (TBits x) (StringtoInt.Binary.neg x val))
               | uo, t => Error (msg "type error in unary expression.")
               end

  end.

(*Test unary *)

(*
Check typecheck_unary.
Compute typecheck_unary Unary_Int (Some (TConst TInt 123)).
Compute typecheck_unary Unary_Int (Some (TConst (TBits 4) 8)).
Compute typecheck_unary Unary_Int (Some (TConst (THexes 2) 16)).
Compute typecheck_unary Unary_Int (Some (TBool)).
Compute typecheck_unary Unary_Int None.
Compute typecheck_unary Unary_Not (Some TBool).
Compute typecheck_unary Unary_Not (Some (TConst TInt 123)).
Compute typecheck_unary Unary_Not None.
Compute typecheck_unary Unary_Tilde (Some (TConst (TBits 4) 8)).
Compute typecheck_unary Unary_Tilde (Some (TConst (TBits 4) (-2))).
Compute typecheck_unary Unary_Tilde (Some (TConst (TBits 1) 0)).
Compute typecheck_unary Unary_Tilde (Some (TConst (TBits 3) 0)).
Compute typecheck_unary Unary_Tilde (Some (TConst (TInt) 3)).
Compute typecheck_unary Unary_Tilde None.
*)
(* need to check both t1 and t2 are const types*)

Definition typecheck_binary (b : binary_operator) (ot1 ot2 : res ty) :=
  match ot1, ot2 with
  | OK t1, OK t2 =>
    match b, t1, t2 with
    (*a + b*)
    | Binary_Add, TConst _ val1, TConst _ val2 => OK (TConst TInt (val1 + val2)) (* const expr*)
    | Binary_Add, TX _, _ => Error (msg "type error in add expression")
    | Binary_Add, _, TX _ => Error (msg "type error in add expression")
    | Binary_Add, _, _ => OK TInt
    (*a - b*)
    | Binary_Sub, TConst _ val1, TConst _ val2 => OK (TConst TInt (val1 - val2)) (* const expr *)
    | Binary_Sub, TX _, _ => Error (msg "type error in sub expression")
    | Binary_Sub, _, TX _ => Error (msg "type error in sub expression")
    | Binary_Sub, _, _ => OK TInt
    (*a * b*)
    | Binary_Mul, TConst _ val1, TConst _ val2 => OK (TConst TInt (val1 * val2)) (* cosnt expr *)
    | Binary_Mul, TX _, _ => Error (msg "type error in mul expression")
    | Binary_Mul, _ ,TX _ => Error (msg "type error in mul expression")
    | Binary_Mul, _, _ => OK TInt
    (*a / b*)
    | Binary_Div, TConst _ val1, TConst _ val2 => OK (TConst TInt (Zdiv val1 val2)) (* const expr *)
    | Binary_Div, TX _, _ => Error (msg "type error in div expression")
    | Binary_Div, _, TX _ => Error (msg "type error in div expression")
    | Binary_Div, _, _ => OK TInt
    (*a % b*)
    | Binary_Mod, TConst _ val1, TConst _ val2 => OK (TConst TInt (Zmod val1 val2)) (* const expr *)
    | Binary_Mod, TX _, _ => Error (msg "type error in mod expression")
    | Binary_Mod, _, TX _ => Error (msg "type error in mod expression")
    | Binary_Mod, _, _ => OK TInt
    (*a && b*)
    | Binary_AndAnd, TBool, TBool => OK TBool
    (*a || b*)
    | Binary_OrOr, TBool, TBool => OK TBool
    (*a & b*)
    | Binary_And, TConst (TBits n1) val1, TConst (TBits n2) val2 => if Nat.eqb n1 n2 then OK (TConst (TBits n1) (StringtoInt.Binary.and n1 val1 val2)) else Error (msg "two bits type have different length during add operation")
    (*a | b*)
    | Binary_Or, TConst (TBits n1) val1, TConst (TBits n2) val2 => if Nat.eqb n1 n2 then OK (TConst (TBits n1) (StringtoInt.Binary.or val1 val2)) else Error (msg "two bits type have different length during or operation")
    (*a ^ b*)
    | Binary_Xor, TConst (TBits n1) val1, TConst (TBits n2) val2 => if Nat.eqb n1 n2 then OK (TConst (TBits n1) (StringtoInt.Binary.xor n1 val1 val2)) else Error (msg "two bits type have different length during xor operation")
    (*a == b*)
    | Binary_EqEq, _, _ => OK TBool
    (*a <> b*)
    | Binary_Neq, _, _ => OK TBool
    (*a < b*)
    | Binary_Les, _, _ => OK TBool
    (*a > b*)
    | Binary_Gre, _, _ => OK TBool
    (*a <= b*)
    | Binary_LesEq, _, _ => OK TBool
    (*a >= b*)
    | Binary_GreEq, _, _ => OK TBool
    (*a << b*)
    | Binary_LesLes, TConst t v1, TConst TInt v2 => OK (TConst TInt (Z.mul v1 (Z.pow 2 v2))) (*const expr*)
    | Binary_LesLes, TX _, _ => Error (msg "type error in left shift operation")
    | Binary_LesLes, _, TX _ => Error (msg "type error in left shift operation")
    | Binary_LesLes, _ , _ => OK TInt
    (*a >> b*)
    | Binary_GreGre, TConst t v1, TConst TInt v2 => OK (TConst TInt (Z.div v1 (Z.pow 2 v2))) (*const expr*)
    | Binary_GreGre, TX _, _ => Error (msg "type error in right shift operation")
    | Binary_GreGre, _, TX _ => Error (msg "type error in right shift operation")
    | Binary_GreGre, _, _ => OK TInt
    (*a ++ b*)
    | Binary_AddAdd, TConst (TBits n1) v1, TConst (TBits n2) v2 => OK (TConst (TBits (n1+n2)) (StringtoInt.Binary.bc n1 n2 v1 v2))
    | Binary_AddAdd, TConst (THexes n1) v1, TConst (THexes n2) v2 => OK (TConst (THexes (n1+n2)) (StringtoInt.Hex.bc n1 n2 v1 v2))
    | Binary_AddAdd, TRegAcc k1 n1 n2, TRegAcc k2 m1 m2 =>
      let test := Nat.eqb k1 k2 && Nat.eqb n2 (m1 + 1) && Nat.leb 0 m2 && Nat.leb m2 m1 && Nat.leb m1 n2 && Nat.leb n2 n1 && Nat.ltb n1 k1 in
      if test then OK (TRegAcc k1 n1 m2)
      else Error (msg "type error during register append")
    | Binary_AddAdd, TFieldAcc_cell id1 k1 n1 n2, TFieldAcc_cell id2 k2 m1 m2 =>
      let test := eqb_string (get_idname id1) (get_idname id2) && Nat.eqb k1 k2 && Nat.eqb m1 (n2 + 1) && Nat.leb 0 n1 && Nat.leb n1 n2 && Nat.leb n2 m1 && Nat.leb m1 m2 && Nat.ltb m2 k1 in
      if test then OK (TFieldAcc_cell id1 k1 n1 m2)
      else Error (msg "type error during field append in cell")
    | Binary_AddAdd, TFieldAcc_protocol k1 n1 n2, TFieldAcc_protocol k2 m1 m2 =>
      let test := Nat.eqb k1 k2 && Nat.eqb m1 (n2 + 1) && Nat.leb 0 n1 && Nat.leb n1 n2 && Nat.leb n2 m1 && Nat.leb m1 m2 && Nat.ltb m2 k1 in
      if test then OK (TFieldAcc_protocol k1 n1 m2)
      else Error (msg "type error during field append in protocol")
    (*hex(n) a*)
    | Binary_Hex, TConst t m, TConst TInt n => if (0 <=? m) && ((Z.of_nat ((length (StringtoInt.Hex.of_Z m)) - 2)) <=? n) then OK (TConst (THexes (N.to_nat (Z.to_N n))) m) else Error (msg "type error during cast to hex")
    (*bit(n) a*)
    | Binary_Bit, TConst t m, TConst TInt n => if (0 <=? m) && ((Z.of_nat ((length (StringtoInt.Binary.of_Z m)) - 2)) <=? n) then OK (TConst (TBits (N.to_nat (Z.to_N n))) m) else Error (msg "type error during cast to bit")
    | _,_,_ => Error (msg "binary operator was not matched to the type")
    end
  | Error e1, _ => Error e1
  | _, Error e2 => Error e2
  end.

(* Test binary*)
(* Todo *)

Fixpoint efield_sum (flds : list (string * nat)) (sum_n : nat) :=
  match flds with
  | nil => sum_n
  | (fid_i, n_i) :: t => efield_sum t (Nat.add sum_n n_i)
  end.

Fixpoint efield_find (fid : string) (flds : list (string * nat)) (sum_n : nat):=
  match flds with
  | nil => Error (msg (String.append fid " was not found in protocol"))
  | (fid_i, n_i) :: t => if (eqb_string fid fid_i) then OK (sum_n, n_i)
                       else efield_find fid t (Nat.add sum_n n_i)
  end.

Definition compare_ofid (ofid : optional_field) (fid : identifier) :=
  match ofid with
  | Optional_Field ofid c => eqb_string (get_idname ofid) (get_idname fid)
  | No_Optional_Field => false
  end.

Definition typecheck_field_expression (pid_envs : pid_scope)
           (id_envs : id_scope) (t : res ty) (fid : identifier) :=
  match t with
  | OK (TX pid) =>
    let protocol := find_scope_id pid pid_envs in
    match protocol with
    | OK (Protocol_Symbol flds ofid statements) =>
      if compare_ofid ofid fid then OK TInt
      else
        let ef := efield_find (get_idname fid) flds 0 in
        match ef with
        | OK (sum_n, n_i) => let n := efield_sum flds 0 in
                            OK (TFieldAcc_cell pid n sum_n (Nat.sub (Nat.add sum_n n_i) 1))
        | Error e' => Error e'
        end
    | Error e'' => Error e''
    end
  | OK _ => Error (msg "expression not support '.' operator")
  | Error e''' => Error e'''
  end.

(*Test field*)
(*Todo*)

Definition typecheck_section_expression (g_envs : g_scope) (envs : id_scope) (tp t1 t2: res ty) :=
  match tp, t1, t2 with
  | OK e1, OK e2, OK e3 =>
    match e1, e2, e3 with
    | TRegAcc n n1 n2, TConst TInt n', TConst TInt n'' =>
      let sn := (find_scope_id Creglen g_envs) in
      match sn with
        | Error e' => Error e'
        | OK n =>
          if (Nat.leb 0 n2) && (Nat.leb n2 n1) && (Nat.ltb n1 n) && (Z.leb 0 n'') && (Z.leb n'' n') && (Z.leb n' (Z.of_N (N.of_nat (n1 - n2)))) then OK (TRegAcc n (n2 + (N.to_nat (Z.to_N n''))) (n2 + (N.to_nat (Z.to_N n')))) else Error (msg "type error in register section expression")
      end
    | TFieldAcc_cell id n n1 n2, TConst TInt n', TConst TInt n'' =>
      if (Nat.leb 0 n1) && (Nat.leb n1 n2) && (Nat.ltb n2 n) && (0 <=? n'') && (n'' <=? n') && (n' <=? (Z.of_N (N.of_nat (Nat.sub n2 n1)))) then OK (TFieldAcc_cell id n (n1 + (N.to_nat (Z.to_N n''))) (n1 + (N.to_nat (Z.to_N n')))) else Error (msg "type error in field section expression in cell")
    | TFieldAcc_protocol n n1 n2, TConst TInt n' , TConst TInt n'' =>
      if (Nat.leb 0 n1) && (Nat.leb n1 n2) && (Nat.ltb n2 n) && (0 <=? n'') && (n'' <=? n') && (n' <=? (Z.of_N (N.of_nat (Nat.sub n2 n1)))) then OK (TFieldAcc_protocol n (n1 + (N.to_nat (Z.to_N n''))) (n1 + (N.to_nat (Z.to_N n')))) else Error (msg "type error in field section expression in protocol")
    | _, _, _ => Error (msg "types were not matched in section expression")
    end
  | Error e1', _, _ => Error e1'
  | _, Error e2', _ => Error e2'
  | _, _, Error e3' => Error e3'
  end.
(*Test section*)
(*Todo*)

Definition typecheck_length_expression (envs : id_scope) (pid_envs : pid_scope) (id : identifier) :=
  let pid := find_scope_id id envs in
  match pid with
  | OK (TX i) => let protocol := find_scope_id i pid_envs in
           match protocol with
           | OK _ => OK TInt
           | Error e' => Error e'
           end
  | OK _ => Error (msg (String.append (get_idname id) " cannot apply length expression"))
  | Error e'' => Error e''
  end.
(*Test length*)
(*Todo*)

Fixpoint typecheck_expression (g_envs: g_scope) (pid_envs: pid_scope)
         (id_envs : id_scope) (e : expression) : res ty:=
  let te:= typecheck_expression g_envs pid_envs id_envs in
  match e with
  | Constant_Expression c =>
    typecheck_constant id_envs c
  | Unary_Expression u e =>
    typecheck_unary u (te e)
  | Binary_Expression b e1 e2 =>
    typecheck_binary b (te e1) (te e2)
  | Field_Expression e fid => typecheck_field_expression pid_envs id_envs (te e) fid
  | Bit_Expression e1 e2 => typecheck_section_expression g_envs id_envs (te e1) (te e2) (te e2)
  | Section_Expression e1 e2 e3 => typecheck_section_expression g_envs id_envs (te e1) (te e2) (te e3)
  | Length_Expression id => typecheck_length_expression id_envs pid_envs id
  | Parentheses_Expression e => te e
  end.


(*-----------statement----------*)

(*Todo*)
Definition get_const_val := fun (c : constant) (id_envs : id_scope) => match typecheck_constant (id_envs) c with
                                          | OK (TConst t' v') => OK v'
                                          | _ => Error (msg "cannot calculate a common expression during type checking")
                                          end.

(*Initialization of L enviorment: p symbol table*)
Fixpoint field_find_id (id : identifier) (index : nat) (flds : list field):=
  match index with
  | O => false
  | S i' =>
    match flds with
    | nil => false
    | (Field id' c) :: t => if eqb_string (get_idname id) (get_idname id') then true
                          else field_find_id id i' t
    end
  end.

Fixpoint trans_fields_raw (flds : list field) (index : nat) (id_envs : id_scope) (whole_flds : list field) :=
  match flds with
  | nil => (true,nil)
  | h :: t => match h with
            | Field id c => if field_find_id id index whole_flds then (false,nil)
                           else let (ok, trans_list) := trans_fields_raw t (S index) id_envs whole_flds in
                                let cval := get_const_val c id_envs in
                                match cval with
                                  | OK v' =>
                                    if (v' >? 0) && ok then (true,((get_idname id),N.to_nat (Z.to_N v')) :: trans_list)
                                    else (false,nil)
                                  | Error _ => (false,nil)
                                end
            end
  end.

Definition trans_protocol_to_symbol (p : protocol) (id_envs : id_scope) : res protocol_symbol :=
  match p with
  | Protocol (Fields flds ofld) statements =>
    let (ok, trans_list) := trans_fields_raw flds 0 id_envs flds in
    if ok then OK (Protocol_Symbol trans_list ofld statements)
    else Error (msg "protocol field error in definition")
  end.
(*Test protocol_to_symbol*)
(*Todo*)

Fixpoint check_reg_overlap (n n1 n2 : nat) (id_envs : id_scope) : bool :=
  match id_envs with
  | nil => true
  | (str, r) :: t => match r with
                   | TRegAcc n' n1' n2' => if (negb (Nat.eqb n' n)) || ((Nat.ltb n1' n2) || (Nat.ltb n1 n2')) then
                                            check_reg_overlap n n1 n2 t
                                          else false
                   | _ => check_reg_overlap n n1 n2 t
                   end
  end.

Definition trans_reg_to_symbol (reg_acc_set : register_access_set) (g_envs : g_scope)
           (g_arg : identifier) (pid_envs : pid_scope) (id_envs : id_scope) (local_envs : id_scope) :=
  match find_scope_id g_arg g_envs with
  | Error e' => Error e'
  | OK n =>
    match reg_acc_set with
    | Register_Access_Set_Section id e1 e2 =>
      match find_scope_id id local_envs with
      | OK _ => Error (msg (String.append (get_idname id) " has been repeatedly defined in current enviorment"))
      | _ => match typecheck_expression g_envs pid_envs id_envs e1, typecheck_expression g_envs pid_envs id_envs e2 with
               | OK (TConst TInt n1), OK (TConst TInt n2) => if (0 <=? n2) && (n2 <=? n1) && (n1 <? (Z.of_N (N.of_nat n))) && (check_reg_overlap n (N.to_nat (Z.to_N n1)) (N.to_nat (Z.to_N n2)) id_envs) then OK (id,TRegAcc n (N.to_nat (Z.to_N n1)) (N.to_nat (Z.to_N n2)))  else Error (msg "register section invalid")
               | _, _ => Error (msg "register index invalid")
               end
      end
    | Register_Access_Set_Bit id e =>
      match find_scope_id id local_envs with
      | OK _ => Error (msg (String.append (get_idname id) " has been repeatedly defined in current enviorment"))
      | _ => match typecheck_expression g_envs pid_envs id_envs e with
               | OK (TConst TInt n') => if (0 <=? n') && (n' <? (Z.of_N (N.of_nat n))) && (check_reg_overlap  n (N.to_nat (Z.to_N n')) (N.to_nat (Z.to_N n')) id_envs) then OK (id,TRegAcc n (N.to_nat (Z.to_N n')) (N.to_nat (Z.to_N n'))) else Error (msg "register bit invalid")
               | _ => Error (msg "register index invalid")
               end
      end
    end
  end.
(*Test trans_reg_to_symbol*)
(*Todo*)

Fixpoint initialization_of_CR (g_envs : g_scope) (list_declaration : list declaration)
         (c_envs r_envs : id_scope) (pid_envs : pid_scope): res (id_scope * id_scope * pid_scope) :=
  match list_declaration with
  | nil => OK (c_envs,r_envs,pid_envs)
  | h :: t =>
    match h with
    | As_Constant (Constant_Declaration cid e) => (*C envs*)
      let ev := match (typecheck_constant c_envs e) with
                | OK (TConst ty' val') => update_id_without_same cid (TConst ty' val') c_envs
                | _ => Error (msg "type error in const declaration")
                end in
      match ev with
      | OK new_c_envs => initialization_of_CR g_envs t new_c_envs r_envs pid_envs
      | Error e' => Error e'
      end
    | As_Protocol (Protocol_Declaration pid p) => (*pid envs*)
      let p_symbol := trans_protocol_to_symbol p c_envs in
      match p_symbol with
      | OK p' => let pv := update_id_without_same pid p' pid_envs in
                  match pv with
                  | OK new_pid_envs => initialization_of_CR g_envs t c_envs r_envs new_pid_envs
                  | Error e'' => Error e''
                  end
      | Error e''' => Error e'''
      end
    | As_Register_Access reg_acc_set => (*R envs*)
      let reg_symbol := trans_reg_to_symbol reg_acc_set g_envs Lreglen pid_envs c_envs r_envs in
      match reg_symbol with
      | OK (id',r') => let pr := update_id_without_same id' r' r_envs in
                        match pr with
                        | OK new_r_envs => initialization_of_CR g_envs t c_envs new_r_envs pid_envs
                        | Error e'''' => Error e''''
                        end
      | Error ee => Error ee
      end
    | As_Layer _ => initialization_of_CR g_envs t c_envs r_envs pid_envs
    end
  end.
(*Test Initialization_of_CR*)
(*Todo*)

Fixpoint update_Lc (n nk : nat) (Lc : id_scope) :=
  match Lc with
  | nil => nil
  | (st,type) :: t =>
    match type with
    | TRegAcc k' n1 n2 =>
      (st,TRegAcc n (Nat.add n1 nk) (Nat.add n2 nk)) :: (update_Lc n nk t)
    | _ => update_Lc n nk t
    end
  end.

Definition update_r_envs (g_envs : g_scope) (La Lb0 Lb1 : id_scope) :=
  let sn := find_scope_id Lreglen g_envs in
  let sk := find_scope_id Creglen g_envs in
  match sn, sk with
  | OK n, OK k =>
    if (Nat.eqb n (Nat.mul k 3)) then
      let new_La := update_Lc n (Nat.mul k 2) La in
      let new_Lb0 := update_Lc n k Lb0 in
      let new_Lb1 := update_Lc n 0 Lb1 in
      OK (List.app (List.app new_La new_Lb0) new_Lb1)
    else
      Error (msg "layer length is not equal to 3 times cell length")
  | _, _ => Error (msg "lack of Lreglen and Creglen definitions")
  end.

Fixpoint initialization_of_CRL (id_envs : id_scope) (pid_envs : pid_scope)
         (list_layer_decl : list layer_declaration) (l_envs : id_scope) := (*CR and local L ?*)
  match list_layer_decl with
  | nil => OK (List.app l_envs id_envs)
  | h :: t => match h with
            | Layer_As_Protocol pid ids =>
              match find_scope_id pid pid_envs with
              | OK protocol_symbol =>
                let snew := update_ids_without_same ids (TX pid) l_envs in
                match snew with
                | OK new_l_envs => initialization_of_CRL id_envs pid_envs t new_l_envs
                | Error e' => Error e'
                end
              | Error e'' => Error e''
              end
            end
  end.
(*Test initialization_of_CRL*)
(*Todo*)

Fixpoint initialization_of_list_reg (g_envs : g_scope) (id_envs : id_scope) (pid_envs : pid_scope) (lc_envs : id_scope)
         (list_reg_acc_set : list register_access_set) :=
  match list_reg_acc_set with
  | nil => OK lc_envs
  | reg_acc_set :: t =>
    let reg_symbol := trans_reg_to_symbol reg_acc_set g_envs Creglen pid_envs id_envs lc_envs in
      match reg_symbol with
      | OK (id',r') => let pr := update_id_without_same id' r' lc_envs in
                        match pr with
                        | OK new_lc_envs => initialization_of_list_reg g_envs id_envs pid_envs new_lc_envs t
                        | Error e' => Error e'
                        end
      | Error e'' => Error e''
      end
  end.

Definition initialization_of_La (g_envs : g_scope) (id_envs : id_scope) (pid_envs : pid_scope)
           (reg_cella : cell_a_register) :=
  match reg_cella with
  | Cell_A_Register list_reg_acc_set => initialization_of_list_reg g_envs id_envs pid_envs empty_id_env list_reg_acc_set
  | No_Cell_A_Register => OK empty_id_env
  end.

Definition initialization_of_Lb0 (g_envs : g_scope) (id_envs : id_scope) (pid_envs : pid_scope)
           (reg_cellb0 : cell_b0_register) :=
  match reg_cellb0 with
  | Cell_B0_Register list_reg_acc_set => initialization_of_list_reg g_envs id_envs pid_envs empty_id_env list_reg_acc_set
  | No_Cell_B0_Register => OK empty_id_env
  end.

Definition initialization_of_Lb1 (g_envs : g_scope) (id_envs : id_scope) (pid_envs : pid_scope)
           (reg_cellb1 : cell_b1_register) :=
  match reg_cellb1 with
  | Cell_B1_Register list_reg_acc_set => initialization_of_list_reg g_envs id_envs pid_envs empty_id_env list_reg_acc_set
  | No_Cell_B1_Register => OK empty_id_env
  end.

Definition initialization_of_Lc (g_envs : g_scope) (id_envs : id_scope) (pid_envs : pid_scope)
         (local_reg_decl : local_register_declaration) :=
  match local_reg_decl with
  | Local_Register_Declaration reg_cella reg_cellb0 reg_cellb1 =>
    let sla := initialization_of_La g_envs id_envs pid_envs reg_cella in
    let slb0 := initialization_of_Lb0 g_envs id_envs pid_envs reg_cellb0 in
    let slb1 := initialization_of_Lb1 g_envs id_envs pid_envs reg_cellb1 in
    (sla, slb0, slb1)
  end.
(*Test initialization_of_CRLLc*)
(*Todo*)

Fixpoint sum_of_flds (flds : list (string * nat)) (n : nat) :=
  match flds with
  | nil => n
  | (st, v) :: t => sum_of_flds t (Nat.add v n)
  end.

Fixpoint initialization_of_fields (g_envs : g_scope) (id_envs : id_scope)
         (pid_envs : pid_scope) (flds : list (string * nat)) (p_envs : id_scope) (sum_ni : nat) (n : nat) :=
  match flds with
  | nil => OK p_envs
  | (st, v) :: t =>
    let np := update_str_without_same st (TFieldAcc_protocol n sum_ni (Nat.sub (Nat.add sum_ni v) 1)) p_envs in
    match np with
    | OK new_p_envs => initialization_of_fields g_envs id_envs pid_envs t new_p_envs (Nat.add sum_ni v) n
    | Error e' => Error e'
    end
  end.

Definition initialization_of_P (g_envs : g_scope) (id_envs : id_scope)
           (pid_envs : pid_scope) (flds : list (string * nat)) (ofld : optional_field) :=
  let sf := initialization_of_fields g_envs id_envs pid_envs flds empty_id_env 0 (sum_of_flds flds 0) in
  match sf with
  | OK p_envs =>
    match ofld with
    | Optional_Field ofid oconst => update_id_without_same ofid TInt p_envs
    | No_Optional_Field => OK p_envs
    end
  | Error e' => Error e'
  end.
(*Test initialization_of_CRLLcP*)
(*Todo*)

Fixpoint typecheck_target_register_access_name (g_envs : g_scope) (id_envs : id_scope)
         (pid_envs : pid_scope) (tra : target_register_access_name) :=
  match tra with
  | Target_Register_Id id =>
    match find_scope_id id id_envs with
    | OK (TRegAcc n n1 n2) => OK (TRegAcc n n1 n2)
    | OK _ => Error (msg (String.append (get_idname id) " is not register access type"))
    | Error e' => Error e'
    end
  | Target_Register_Section tra' e1 e2 =>
    let srt := typecheck_target_register_access_name g_envs id_envs pid_envs tra' in
    let st1 := typecheck_expression g_envs pid_envs id_envs e1 in
    let st2 := typecheck_expression g_envs pid_envs id_envs e2 in
    match srt, st1, st2 with
    | OK (TRegAcc n m1 m2), OK (TConst TInt k1), OK (TConst TInt k2) =>
      if (0 <=? k2) && (k2 <=? k1) && (k1 <=? (Z.of_N (N.of_nat m1)) - (Z.of_N (N.of_nat m2))) then
        OK (TRegAcc n (Nat.add m2 (N.to_nat (Z.to_N k1))) (Nat.add m2 (N.to_nat (Z.to_N k2))))
      else
        Error (msg "Target Register Section invalid")
    | _, _, _ => Error (msg "Target Register Section invalid")
    end
  | Target_Register_Bit tra' e =>
    let srt := typecheck_target_register_access_name g_envs id_envs pid_envs tra' in
    let st := typecheck_expression g_envs pid_envs id_envs e in
    match srt, st with
    | OK (TRegAcc n m1 m2), OK (TConst TInt k) =>
      if (0 <=? k) && (k <=? (Z.of_N (N.of_nat m1)) - (Z.of_N (N.of_nat m2))) then
        OK (TRegAcc n (Nat.add m2 (N.to_nat (Z.to_N k))) (Nat.add m2 (N.to_nat (Z.to_N k))))
      else
        Error (msg "Target Register Bit invalid")
    | _, _ => Error (msg "Target Register Bit invalid")
    end
  end.

Fixpoint typecheck_move_register_access_name (g_envs : g_scope) (id_envs : id_scope)
         (pid_envs : pid_scope) (mra : move_register_access_name) :=
  match mra with
  | Move_Register_Single tra => typecheck_target_register_access_name g_envs id_envs pid_envs tra
  | Move_Register_Double mra' tra =>
    let smrt := typecheck_move_register_access_name g_envs id_envs pid_envs mra' in
    let strt := typecheck_target_register_access_name g_envs id_envs pid_envs tra in
    match smrt, strt with
    | OK (TRegAcc n m1 m2), OK (TRegAcc n' n1 n2) =>
      if (Nat.eqb n n') && (Nat.eqb m2 (S n1)) then OK (TRegAcc n m1 n2)
      else Error (msg "Move Register invalid")
    | _, _ => Error (msg "Move Register invalid")
    end
  end.

Fixpoint typecheck_instructions (g_envs : g_scope) (id_envs : id_scope)
         (pid_envs : pid_scope) (ins : list instruction) :=
  match ins with
  | nil => OK true
  | h :: t =>
    let test :=
        match h with
        | Set_Instruction tra e =>
          let srt := typecheck_target_register_access_name g_envs id_envs pid_envs tra in
          let st := typecheck_expression g_envs pid_envs id_envs e in
          let test1 :=
              match srt, st with
              | OK (TRegAcc n' n1 n2), OK (TConst t' m) =>
                let len := length_of_Z m in
                Nat.leb len (S (Nat.sub n1 n2))
              | _, _ => false
              end
          in
          if test1 then OK true else Error (msg "type error in set instruction")
        | Mov_Instruction mra e =>
          let smt := typecheck_move_register_access_name g_envs id_envs pid_envs mra in
          let st := typecheck_expression g_envs pid_envs id_envs e in
          let test2 := 
              match smt with
              | OK (TRegAcc n' n1 n2) =>
                match st with
                | OK (TRegAcc n_r r' r'') => Nat.eqb (Nat.sub n1 n2) (Nat.sub r' r'')
                | OK (TFieldAcc_cell id' n_f f' f'') => Nat.eqb (Nat.sub n1 n2) (Nat.sub f'' f')
                | OK (TFieldAcc_protocol n_f f' f'') => Nat.eqb (Nat.sub n1 n2) (Nat.sub f'' f')
                | _ => false
                end
              | _ => false
              end
          in
          if test2 then OK true else Error (msg "type error in move instruction")
        | Lg_Instruction tra e1 e2 =>
          let srt := typecheck_target_register_access_name g_envs id_envs pid_envs tra in
          let st1 := typecheck_expression g_envs pid_envs id_envs e1 in
          let st2 := typecheck_expression g_envs pid_envs id_envs e2 in
          match srt, st1, st2 with
          | OK (TRegAcc n' n1 n2), OK _, OK _ => OK true
          | _, _, _ => Error (msg "type error in lg instruction")
          end
        | Eq_Instruction tra e1 e2 =>
          let srt := typecheck_target_register_access_name g_envs id_envs pid_envs tra in
          let st1 := typecheck_expression g_envs pid_envs id_envs e1 in
          let st2 := typecheck_expression g_envs pid_envs id_envs e2 in
          match srt, st1, st2 with
          | OK (TRegAcc n' n1 n2), OK _, OK _ => OK true
          | _, _, _ => Error (msg "type error in eq instruction")
          end
        end
    in
    match test with
    | OK _ => typecheck_instructions g_envs id_envs pid_envs t
    | Error e' => Error e'
    end
  end.

Definition typecheck_action_statement (g_envs : g_scope) (id_envs : id_scope)
           (pid_envs : pid_scope) (act : action_statement) :=
  match act with
  | Action_Statement list_instruction =>
    typecheck_instructions g_envs id_envs pid_envs list_instruction
  end.

Fixpoint typecheck_protocol_if_branches (g_envs : g_scope) (id_envs : id_scope)
         (pid_envs : pid_scope) (list_pro_if_branch : list protocol_if_branch) (f : list protocol_statement -> res bool) :=
  match list_pro_if_branch with
  | nil => OK true
  | h :: t =>
    let test :=
        match h with
        | Protocol_If_Branch e stas =>
          match typecheck_expression g_envs pid_envs id_envs e with
          | OK TBool => f stas
          | _ => Error (msg "type error in protocol if condition")
          end
        end
    in
    match test with
    | OK _ => OK true
    | Error e' => Error e'
    end
  end.

Definition typecheck_protocol_default_branch (g_envs : g_scope) (id_envs : id_scope)
           (pid_envs : pid_scope) (pro_de_branch : protocol_default_branch) (f : list protocol_statement -> res bool):=
  let test :=
      match pro_de_branch with
      | Protocol_Default_Branch stas => f stas
      | Protocol_No_Default_Branch => OK true
      end
  in
  match test with
  | OK _ => OK true
  | Error e' => Error e'
  end.

Definition typecheck_protocol_if_statement (g_envs : g_scope) (id_envs : id_scope)
           (pid_envs : pid_scope) (if_stas : protocol_if_statement) (f : list protocol_statement -> res bool) :=
  match if_stas with
  | Protocol_If_Statement list_pro_if_branch pro_de_branch =>
    let t1 := typecheck_protocol_if_branches g_envs id_envs pid_envs list_pro_if_branch f in
    let t2 := typecheck_protocol_default_branch g_envs id_envs pid_envs pro_de_branch f in
    match t1 with
    | OK _ => OK true
    | Error e' => Error e'
    end
  end.

Fixpoint typecheck_statement_in_a_protocol (g_envs : g_scope) (id_envs : id_scope)
         (pid_envs : pid_scope) (timer : nat) (len : nat) (statements : list protocol_statement) : res bool :=
  (*cannot guess decreasing, use timer to solve*)
  match timer with
  | O => Error (msg "Timed out in protocol statements")
  | S timer' =>
    let f := typecheck_statement_in_a_protocol g_envs id_envs pid_envs timer' len in
    match statements with
    | nil => OK true
    | h :: t =>
      let tmp :=
          match h with
          | Protocol_If pro_if_sta => typecheck_protocol_if_statement g_envs id_envs pid_envs pro_if_sta f
          | Protocol_Next_Header id =>
            match find_scope_id id pid_envs with
            | OK _ => OK true
            | Error e' => Error e'
            end
          | Protocol_Length c =>
            let test1 :=
                match typecheck_constant id_envs c with
                | OK (TConst TInt n) => (n * 8 >=? (Z.of_N (N.of_nat len)))
                | _ => false
                end
            in
            if test1 then OK true else Error (msg "type error in protocol_length statement")
          | Protocol_Bypass c =>
            let test2 :=
                match typecheck_constant id_envs c with
                | OK (TConst TInt n) => if (n =? 0) || (n =? 1) || (n =? 2) then true else false
                | _ => false
                end
            in
            if test2 then OK true else Error (msg "type error in protocol_bypass statement")
          | Protocol_Action act =>
            typecheck_action_statement g_envs id_envs pid_envs act
          end
      in
      match tmp with
      | OK _ => f t
      | Error e'' => Error e''
      end
    end
  end.

Fixpoint typecheck_protocols_statement (g_envs : g_scope) (id_envs : id_scope)
         (pid_envs : pid_scope) (list_layer_decl : list layer_declaration) :=
  match list_layer_decl with
  | nil => OK true
  | h :: t =>
    match h with
    | Layer_As_Protocol pid ids => match find_scope_id pid pid_envs with
                                  | OK ps =>
                                    match ps with
                                    | Protocol_Symbol flds ofld statements =>
                                      let sp := initialization_of_P g_envs id_envs pid_envs flds ofld in
                                      let len := sum_of_flds flds 0 in
                                      match sp with
                                      | OK p_envs =>
                                        let new_id_envs := List.app p_envs id_envs in (*CRLLaP*)
                                        match typecheck_statement_in_a_protocol g_envs new_id_envs pid_envs 1000%nat len statements with
                                          | OK _ => typecheck_protocols_statement g_envs id_envs pid_envs t
                                          | Error e' => Error e'
                                        end
                                      | Error e'' => Error e''
                                      end
                                    end
                                  | Error e''' => Error e'''
                                  end
    end
  end.

Fixpoint typecheck_layer_if_branches (g_envs : g_scope) (id_envs : id_scope)
         (pid_envs : pid_scope) (list_la_if_branch : list layer_if_branch) (f : list layer_statement -> res bool) :=
  match list_la_if_branch with
  | nil => OK true
  | h :: t =>
    let test :=
        match h with
        | Layer_If_Branch e stas =>
          match typecheck_expression g_envs pid_envs id_envs e with
          | OK TBool => f stas
          | OK _ => Error (msg "type error in layer if condition")
          | Error e'' => Error e''
          end
        end
    in
    match test with
    | OK _ => typecheck_layer_if_branches g_envs id_envs pid_envs t f
    | Error e' => Error e'
    end
  end.

Definition typecheck_layer_default_branch (g_envs : g_scope) (id_envs : id_scope)
           (pid_envs : pid_scope) (la_de_branch : layer_default_branch) (f : list layer_statement -> res bool):=
  match la_de_branch with
  | Layer_Default_Branch stas => f stas
  | Layer_No_Default_Branch => OK true
  end.

Definition typecheck_layer_if_statement (g_envs : g_scope) (id_envs : id_scope)
           (pid_envs : pid_scope) (if_stas : layer_if_statement) (f : list layer_statement -> res bool) :=
  match if_stas with
  | Layer_If_Statement list_la_if_branch la_de_branch =>
    let t1 := typecheck_layer_if_branches g_envs id_envs pid_envs list_la_if_branch f in
    let t2 := typecheck_layer_default_branch g_envs id_envs pid_envs la_de_branch f in
    match t1 with
    | OK _ => t2
    | Error e' => Error e'
    end
  end.

Fixpoint typecheck_layer_statement (g_envs : g_scope) (id_envs : id_scope)
         (pid_envs : pid_scope) (timer : nat) (cell : string) (statements : list layer_statement) :=
  match timer with
  | O => Error (msg "Timed out in layer statements")
  | S timer' =>
    let f := typecheck_layer_statement g_envs id_envs pid_envs timer' cell in
    match statements with
    | nil => OK true
    | h :: t =>
      let tmp :=
          match h with
          | Layer_If la_if_sta => typecheck_layer_if_statement g_envs id_envs pid_envs la_if_sta f
          | Layer_Next_Header id =>
            if (eqb_string cell "A") then
              match find_scope_id id pid_envs with
              | OK _ => OK true
              | Error e' => Error e'
              end
            else Error (msg "unsupport keyword in current cell")
          | Layer_Length e =>
            if (eqb_string cell "A") then
              match typecheck_expression g_envs pid_envs id_envs e with
              | OK (TConst TInt n) => OK true
              | OK (TInt) => OK true
              | OK _ => Error (msg "invalid expression type in layer length")
              | Error e' => Error e'
              end
            else Error (msg "unsupport keyword in current cell")
          | Layer_Bypass c =>
            if (eqb_string cell "A") then
              match typecheck_constant id_envs c with
              | OK (TConst TInt n) => if (n =? 0) || (n =? 1) || (n =? 2) then OK true else Error (msg "invalid n in layer bypass")
              | _ => Error (msg "invalid constant in layer bypass")
              end
            else Error (msg "unsupport keyword in current cell")
          | Layer_As_Action act =>
            typecheck_action_statement g_envs id_envs pid_envs act
          end
      in
      match tmp with
      | OK _ => f t
      | Error e'' => Error e''
      end
    end
  end.

Definition typecheck_cell_a_action (g_envs : g_scope) (id_envs : id_scope)
           (pid_envs : pid_scope) (cell_a_act : cell_a_action) :=
  match cell_a_act with
  | Cell_A_Action statements =>
    typecheck_layer_statement g_envs id_envs pid_envs 1000%nat "A" statements
  | No_Cell_A_Action => OK true
  end.

Definition typecheck_cell_b0_action (g_envs : g_scope) (id_envs : id_scope)
           (pid_envs : pid_scope) (cell_b0_act : cell_b0_action) :=
  match cell_b0_act with
  | Cell_B0_Action statements =>
    typecheck_layer_statement g_envs id_envs pid_envs 1000%nat "B0" statements
  | No_Cell_B0_Action => OK true
  end.

Definition typecheck_cell_b1_action (g_envs : g_scope) (id_envs : id_scope)
           (pid_envs : pid_scope) (cell_b1_act : cell_b1_action) :=
  match cell_b1_act with
  | Cell_B1_Action statements =>
    typecheck_layer_statement g_envs id_envs pid_envs 1000%nat "B1" statements
  | No_Cell_B1_Action => OK true
  end.

Definition typecheck_local_action (g_envs : g_scope) (CRLLa CRLLb0 CRLLb1 : id_scope)
         (pid_envs : pid_scope) (local_act : local_action) :=
  match local_act with
  | Local_Action cell_a_act cell_b0_act cell_b1_act =>
    let t1 := typecheck_cell_a_action g_envs CRLLa pid_envs cell_a_act in
    let t2 := typecheck_cell_b0_action g_envs CRLLb0 pid_envs cell_b0_act in
    let t3 := typecheck_cell_b1_action g_envs CRLLb1 pid_envs cell_b1_act in
    match t1 with
    | OK _ =>
      match t2 with
      | OK _ => t3
      | Error e' => Error e'
      end
    | Error e'' => Error e''
    end
  end.

Fixpoint typecheck_layer (g_envs : g_scope) (c_envs r_envs : id_scope)
         (pid_envs : pid_scope) (list_declaration : list declaration) : res bool :=
  match list_declaration with
  | nil => OK true
  | h :: t =>
    match h with
    | As_Layer (Layer_Action lid local_reg_decl list_layer_decl local_act) =>
      let id_envs := List.app r_envs c_envs in (*CR*)
      let sl := initialization_of_CRL id_envs pid_envs list_layer_decl empty_id_env in
      match sl with
      | OK new_id_envs => (*CRL*)
        let sa_sb0_sb1 := initialization_of_Lc g_envs new_id_envs pid_envs local_reg_decl in
          match sa_sb0_sb1 with
          | (OK new_id_envs_La, OK new_id_envs_Lb0, OK new_id_envs_Lb1) => (*L_A L_B0 L_B1*)
            let new_id_envs_CRLLa := List.app new_id_envs_La new_id_envs in      (*CRLL_A*)
            let new_id_envs_CRLLb0 := List.app new_id_envs_Lb0 new_id_envs in    (*CRLL_B0*)
            let new_id_envs_CRLLb1 := List.app new_id_envs_Lb1 new_id_envs in    (*CRLL_B1*)
            let t1 := typecheck_protocols_statement g_envs new_id_envs_CRLLa pid_envs list_layer_decl in
            let t2 := typecheck_local_action g_envs new_id_envs_CRLLa new_id_envs_CRLLb0 new_id_envs_CRLLb1 pid_envs local_act in
            match t1, t2 with
              | OK _, OK _ => 
                match update_r_envs g_envs new_id_envs_La new_id_envs_Lb0 new_id_envs_Lb1 with
                | OK new_r_envs =>
                  typecheck_layer g_envs c_envs new_r_envs pid_envs t
                | Error e' => Error e'
                end
              | Error e1, _ => Error e1
              | _, Error e2 => Error e2
            end
          | (Error ea, _, _) => Error ea
          | (_, Error eb0, _) => Error eb0
          | (_, _, Error eb1) => Error eb1
          end
      | Error e'' => Error e''
      end
    | _ => typecheck_layer g_envs c_envs r_envs pid_envs t
    end
  end.

Definition typecheck_program (p : program) : res bool :=
  match p with
  | Program (Layer_Register_Length c1) (Cell_Register_Length c2)  pset lset list_declaration =>
    match (get_const_val c1 empty_id_env), (get_const_val c2 empty_id_env) with
    | OK v1, OK v2 =>
      if (v1 >? 0) && (v2 >? 0) then
        let g_envs : g_scope := ("Lreglen", N.to_nat (Z.to_N (Z.mul v1 8))) :: ("Creglen", N.to_nat (Z.to_N (Z.mul v2 8))) :: nil in
        let CR_Env := initialization_of_CR g_envs list_declaration empty_id_env empty_id_env empty_pid_env in
        match CR_Env with
        | OK (c_envs, r_envs, pid_envs) =>
          typecheck_layer g_envs c_envs r_envs pid_envs list_declaration
        | Error e' => Error e'
        end
      else
        Error (msg "layer and cell length must be positive")
    | _, _ => Error (msg "invalid layer/cell value")
    end
  end.

(*Test Program*)
(*Todo*)

Definition typechecker (p : program) :=
  match typecheck_program p with
  | OK _ => OK p
  | Error e => Error e
  end.

