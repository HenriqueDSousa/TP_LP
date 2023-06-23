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
            | ("<=", IntV i1, IntV i2) => IntV (i1 <= i2)
            | ("<", IntV i1, IntV i2) => IntV (i1 < i2)
						| (";" , _ , _) => v2
            | ("&&", BoolV b1, BoolV b2) => BoolV(b1 andalso b2)
            | ("=", e1, e2) =>  BoolV(e1 = e2)
            | ("!=", e1, e2) => BoolV(not (e1 = e2)) 
            | ("::", e1, ESeq _) => SeqV((eval e1 env)::[])
            | ("::", e1, e2) =>
                let
                  val s1 = eval e1 env;
                  val s2 = checkList(eval e2 env)
                in
                  SeqV(s1::s2)
                end
            | _ => raise Impossible
						end
    | Item(idx, e2) =>
        let
          val seq = checkList(eval e2 env)
        in
          eval (List.nth(seq, idx-1) env
        end
    | If(exp1, exp2, exp3) => if eval e1 env = BoolV true then eval e2 env else eval e3 env
    | Match(e, options) => 
        let
          val v1 = eval e env;
          val found = List.find(fn (x) => (#1 x) = SOME(v1)) li;
          val notFound = List.find(fn (x) => (#1 x) = NONE) li;
        in 
          case found of
               SOME(some, value) => eval value
             | NONE => eval (#2 (Option.getOpt(notFound, (NONE, IConst 0))))
        end
		| Let(x, e1, e2) =>
				let
					val v = eval e1 env
					val env2 = (x,v) :: env
				in
					eval e2 env2
				end
		| _ => raise Impossible

