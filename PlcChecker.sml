(* PlcChecker *)


exception EmptySeq (*A sequência de entrada não contém nenhum elemento*)
exception UnknownType (*É usada nas situações onde nenhuma das específicas se encaixa.*)
exception NotEqTypes(*Se os tipos usados numa comparação são dnoterentes.*)
exception WrongRetType(*O tipo de retorno da função não condiz com o corpo da mesma.*)
exception DiffBrTypes(*Os tipos da expressões dos possíveis caminhos de um If divergem*)
exception IfCondNotBool(*A condição do if não é booleana*)
exception NoMatchResults(*Não há resultados para a expressão match*)
exception MatchResTypeDiff(*O tipo de algum dos casos em match difere dos demais*)
exception MatchCondTypesDiff(*O tipo das opções de match difere do tipo da expressão passada para Match*)
exception CallTypeMisM(*Você está passando pra uma chamada de função um tipo diferente do qual ela suporta*)
exception NotFunc(*Você está tentando chamar algo que não é uma função.*)
exception ListOutOfRange(*Tentativa de acessar um elemento fora dos limites da lista*)
exception OpNonList(*Tentativa de acessar um elemento em uma expressão que não é uma lista.*)

    

fun areAllRetTypesEqual (retTypes: plcType list) = foldl (fn (a, (areAllSame, t1)) => (areAllSame andalso t1 = a, t1)) (true, (hd retTypes)) retTypes;
fun notNone (expa, _) : bool = case expa of NONE => false | SOME x => true;



fun allTypesMatch (types : plcType list):bool = 
	case types of
		  [] => true
		| x::xs =>
			let
				val type1 = x

				fun checkType [] = true
				  | checkType (y::ys) = if type1 = y then checkType ys else false
			in
				checkType xs
			end;
		 

fun teval (e:expr) (env: plcType env) : plcType =
	case e of
		  ConI _ => IntT
		| ConB _ => BoolT
		| ESeq(SeqT t) => SeqT t
		| Var x => lookup env x
		| Let(x, e1, e2) =>

				let
					val t = teval e1 env
					val env' = (x,t)::env
				in
					teval e2 env'
				end
		
		(* recursive funcition *)
		| Letrec(function, argType, varName, returnType, e1, e2) =>
			
				let 
					val t1 = teval e1 ((function, FunT(argType, returnType))::(varName, argType)::env);
            		val t2 = teval e2 ((function, FunT(argType, returnType))::env);
				in
					if returnType = t1 then t2 else raise WrongRetType
				end

		| Prim1(opr, e1) =>
				let
					val t1 = teval e1 env
				in
					case (opr, t1) of
						 ("print", _) => ListT []

						| ("-", IntT) => t1
				  		| ("-", _) => raise UnknownType

						| ("!", BoolT) => t1
				  		| ("!", _) => raise UnknownType
					
						| ("hd", SeqT x1) => x1
						| ("hd", _) => raise OpNonList

						| ("tl", SeqT x1) => t1
						| ("tl", _) => raise OpNonList

						| ("ise", SeqT _ ) => BoolT
						| ("ise", _ ) => raise UnknownType

						| _ => raise UnknownType

				end
		| Prim2(opr, e1, e2) =>
				
				let
					val t1 = teval e1 env
					val t2 = teval e2 env
				in
					case (opr, t1, t2) of
					  ("*" , IntT, IntT) => t1
					| ("*", _, _) => raise UnknownType	
					
					| ("/" , IntT, IntT) => t1
					| ("/", _, _) => raise UnknownType	

					| ("+" , IntT, IntT) => t1
					| ("+", _, _) => raise UnknownType	

					| ("-" , IntT, IntT) => t1
					| ("-", _, _) => raise UnknownType

					| ("<", IntT, IntT)	=> BoolT
					| ("<", _, _) => raise NotEqTypes
					
					| ("<=", IntT, IntT) => BoolT
					| ("<=", _, _) => raise NotEqTypes

					| ("=", IntT, IntT) => BoolT
					| ("=", BoolT, BoolT) => BoolT
					| ("=", SeqT x1, SeqT x2) => BoolT
					| ("=", _, _) => raise NotEqTypes

					| ("!=", IntT, IntT) => BoolT
					| ("!=", BoolT, BoolT) => BoolT
					| ("!=", SeqT x1, SeqT x2) => BoolT
					| ("!=", _, _) => raise NotEqTypes

					| (";" , _ , _) => t2
					
					| ("&&", BoolT, BoolT)  => BoolT
					| ("&&", _, _) => raise NotEqTypes

					(*verificar*)

					| ("::", SeqT ta, SeqT tb) =>
					 if (ta = tb) 
					 then SeqT(ta)
					 else raise NotEqTypes

					| ("::", ta, tb) =>  
						if SeqT(ta) = tb 
						then SeqT(ta)
						else raise NotEqTypes

					| _   =>  raise UnknownType

					
				end

		(* If *)
		| If(e1, e2, e3) =>

			let
				val t1 = teval e1 env
				val t2 = teval e2 env
				val t3 = teval e3 env
			in
				if t1 = BoolT then 
				
				(if t2 = t3 then t2 else raise DiffBrTypes)

				else raise IfCondNotBool
			end

		| Match(_, []) => raise NoMatchResults
	
		| Match(e, conds: (expr option * expr) list) => 
        let

			(* tipos de retornos *)
            val condsRetTypes = map (fn (_, r) => teval r env) conds;
            val (sameRet, tRes) = areAllRetTypesEqual condsRetTypes;
            val condsExceptNone = (List.filter notNone conds); 

			(* tipos das condicoes *)
            val condTypes = map (fn (SOME c, _) => teval c env | (_,_) => raise UnknownType) condsExceptNone;
            val (sameCond, tCond) = areAllRetTypesEqual(condTypes);
            val eType = teval e env;
        in
            if sameRet = false 
            then raise MatchResTypeDiff 
            else if (sameCond = false orelse eType <> tCond)
            then raise MatchCondTypesDiff
            else tRes
        end

		| Call(Var(e2), e1) => 
            let
                val mayBeFunType = lookup env e2;
                val t1 = teval e1 env;
            in 
                case mayBeFunType of FunT(argT, retT) => if t1 = argT then retT else raise CallTypeMisM 
                    | _ => raise NotFunc
            end

        | Call(Call a, e1) => 
            let 
                val x = teval (Call a) env 
            in 
                case x of FunT(_, r) => r 
                    | _ => raise NotFunc
            end 

        | Call(_, _) => raise NotFunc 

		(* List *)
		| List [] => ListT []
		| List (l: expr list) => ListT(map( fn(elem) => teval elem env) l)	 

		(* Item *)

		| Item(_, List []) => raise EmptySeq
		
		(* O item é indexado a partir do index 1 *)
		| Item(i , List l) =>
			if (i > 0 andalso i <= List.length(l)) 
			then teval (List.nth(l, i-1)) env
			else raise ListOutOfRange

		| Item(i, e1) =>
			let
				val t1 = teval e1 env
			in
				case t1 of 
					
					 ListT li => 
					 	if (i > 0 andalso i <= List.length(li)) 
						then List.nth(li, i - 1) 
						else raise ListOutOfRange
					
					| _ => raise OpNonList
			end
		
		| Anon(t, name, e1) => FunT(t, teval e1 ((name, t)::env))

		| _   =>  raise UnknownType
	
