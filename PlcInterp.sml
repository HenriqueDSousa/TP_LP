(* PlcInterp *)

exception Impossible
exception HDEmptySeq
exception TLEmptySeq
exception ValueNotFoundInMatch
exception NotAFunc


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
                (case seq of
                   SeqV [] => raise HDEmptySeq
                   | SeqV (x::xs) => x
                   | _ => raise Impossible)
            | ("tl", seq) =>
                (case seq of
                   SeqV [] => raise TLEmptySeq
                   | SeqV (x::xs) => SeqV(xs)
                   | _ => raise Impossible)
            | ("ise", seq) =>
                (case seq of
                   SeqV [] => BoolV true
                   | SeqV _ => BoolV false
                   | _ => raise Impossible)
						| _ => raise Impossible
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
            | ("<=", IntV i1, IntV i2) => BoolV (i1 <= i2)
            | ("<", IntV i1, IntV i2) => BoolV (i1 < i2)
						| (";" , _ , _) => v2
            | ("&&", BoolV b1, BoolV b2) => BoolV(b1 andalso b2)
            | ("=", e1, e2) =>  BoolV(e1 = e2)
            | ("!=", e1, e2) => BoolV(not (e1 = e2)) 
            | ("::", e1, SeqV []) => SeqV(e1::[])
            | ("::", e1, e2) =>
                let
                  val s2 = checkList(e2)
                in
                  SeqV(e1::s2)
                end
            | _ => raise Impossible
						end
    | Item(idx, e2) =>
        let
          val seq = checkList(eval e2 env)
        in
          List.nth(seq, idx-1)
        end
    | If(e1, e2, e3) => if eval e1 env = BoolV true then eval e2 env else eval e3 env

    | Match(e1, hd::options: (expr option * expr) list) => 
        
        let
          val ve1 = eval e1 env;
          val (m, a) = hd
        in
          case m of
            SOME e2 => if ve1 = eval e2 env then 
                        eval a env 
                      else if options = [] then 
                        raise ValueNotFoundInMatch 
                      else 
                        eval(Match(e1, options)) env
            | NONE => eval a env
        end


		| Let(x, e1, e2) =>
				let
					val v = eval e1 env
					val env2 = (x,v)::env
				in
					eval e2 env2
				end
    | Anon(_, str, e) => Clos("", str, e, env)

    | Letrec(fname, _, argname, _, e1, e2) =>

        let
            val closure = Clos(fname, argname, e1, env)
            val env2 = (fname, closure) :: env
        in
            eval e2 env2
        end

    | Call(Var vf, e) => let 
          val fv = lookup env vf
        in
          case fv of
            Clos(vf, x, e1, fSt) => let
              val ve1 = eval e env;
              val env' = (x, ve1) :: (vf, fv) :: fSt
            in
              eval e1 env'
            end
            | _ => raise NotAFunc
        end 

    | Call(Call f, e) => 
        
        let 
          val vf = eval (Call f) env;
        in
          case vf of
            Clos(f, x, e1, fSt) => let
              val ve1 = eval e env;
              val env' = (x, ve1) :: (f, vf) :: fSt
            in
              eval e1 env'
            end
            | _ => raise NotAFunc
        end 

    | _ => raise Impossible
