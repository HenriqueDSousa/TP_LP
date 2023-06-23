(* PlcChecker *)

use "Environ.sml";
use "Absyn.sml";


exception EmptySeq (*A sequência de entrada não contém nenhum elemento*)
exception UnknownType (*É usada nas situações onde nenhuma das específicas se encaixa.*)
exception NotEqTypes(*Se os tipos usados numa comparação são diferentes.*)
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
					| ("::", SeqT x1, SeqT x2) => if x1 = x2 then SeqT x1 else raise NotEqTypes
					(*| ("::", SeqT x1, ESeq(SeqT x2)) => if x2 = SeqT x1 then SeqT x1 else raise NotEqTypes*)
					| ("::", _, _) => raise UnknownType

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
		| Match(e0, conditions: (expr option * expr) list) =>
			
			
			let
				(* tipos de retorno das condicoes *)
				val conditionsRetTypes = map( fn(_,res) => teval res env) conditions 
				(* tipos de argumentos das condicoes *)
				val conditionsCondTypes = map(fn (SOME cond,_) => teval cond env | (_,_)=> raise UnknownType) conditions 
				
				val t1 = teval e0 env

				val sameRet = allTypesMatch conditionsRetTypes
				val sameCond = allTypesMatch conditionsCondTypes
			in	

				
				if sameRet = false 
				then raise MatchResTypeDiff
				else if (sameCond = false orelse t1 <> (List.hd(conditionsCondTypes)))
				then raise MatchCondTypesDiff
				
				(*se todos retornos e argumentos tiverem os mesmos tipos*)
				else
				
				List.hd(conditionsRetTypes)

			
			end

		| Call (e1, e2) =>
			let in 
			case (e1, e2) of

				(* chamada de funcao *)
				 (Var(f), exp) => 
					let
						val funcao = lookup env f;
						val tipo = teval exp env;
					in
						case funcao of 

							 FunT(arg, ret) => 
							 	if tipo = arg then arg else raise CallTypeMisM
							 
							| _ => raise NotFunc 
					end
				
				(* funcoes compostas *)
				| ((Call g), _) =>
					let
						val composedFunct = teval (Call g) env 
					in
						case composedFunct of 
							 FunT(_, num) =>  num
						   | _ => raise NotFunc
					end
				
				| (_ , _) => raise NotFunc 
			end

		(* List *)
		| List [] => ListT []
		| List (l: expr list) => ListT(map( fn(elem) => teval elem env) l)	 

		(* Item *)

		| _   =>  raise UnknownType
	
	val expr0 = List [ConI 1, ConI 2, ConI 12];

	teval expr0 [];

