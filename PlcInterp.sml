(* PlcInterp *)

exception Impossible
exception HDEmptySeq
exception TLEmptySeq
exception ValueNotFoundInMatch
exception NotAFunc

(** fun eseqEval(value: plcType) : plcVal  =
  case value of
       IntT => SeqV ([] : IntV list)
     | BoolT => SeqV ([] : BoolV list)
     | FunT t1 * t2 => 
     | ListT lt => 
         case lt of 
              IntT => Seq  
**)

fun checkInt(value: plcVal) : int =
  case value of
       IntV i => i
     | _ => raise Impossible

fun checkBool(value: plcVal) : bool =
  case value of
       BoolV b => b
     | _ => raise Impossible

fun checkList(value: plcVal) : plcVal list =
  case value of
       SeqV s => s
     | ListV l => l
     | _ => raise Impossible


fun eval (e:expr) (env:plcVal env) : plcVal =
	case e of
		  ConI i => IntV i
    | ConB b => BoolV b
    | ESeq _ => SeqV []
    | List [] => ListV []
    | List (x::xs : expr list) =>
        let
          val element1 = eval x env;
          val element2 = checkList(eval (List xs) env);
        in
          ListV (element1::element2)
		    end
    | Var x => lookup env x
		| Prim1(opr, e1) =>
				let
					val v1 = eval e1 env
				in
					case (opr, v1) of
						  ("-", IntV i) => IntV (~i)
            | ("!", BoolV b) => BoolV (not b)
						| ("print", _) =>
										let
											val s = val2string v1
										in
											print(s^"\n"); ListV []
										end
            | ("hd", seq) =>
                case seq of
                     SeqV [] => raise HDEmptySeq
                   | SeqV (x::xs) => x
                   | _ => raise Impossible
            | ("tl", seq) =>
                case seq of
                     SeqV [] => raise TLEmptySeq
                   | SeqV (x::xs) => SeqV(xs)
                   | _ => raise Impossible
            | ("ise", seq) =>
                case seq of
                     SeqV [] => BoolV true
                   | SeqV _ => BoolV false
                   | _ => raise Impossible
						| _   => raise Impossible
						end
		| Prim2(opr, e1, e2) =>
				let
					val v1 = eval e1 env
					val v2 = eval e2 env
				in
					case (opr, v1, v2) of
						  ("*" , IntV i1, IntV i2) => IntV (i1 * i2)
						| ("/" , IntV i1, IntV i2) => IntV (i1 div i2)
						| ("+" , IntV i1, IntV i2) => IntV (i1 + i2)
						| ("-" , IntV i1, IntV i2) => IntV (i1 - i2)
						| (";" , _ , _) => v2
						| _ => raise Impossible
						end
		| Let(x, e1, e2) =>
				let
					val v = eval e1 env
					val env2 = (x,v) :: env
				in
					eval e2 env2
				end
		| _ => raise Impossible
