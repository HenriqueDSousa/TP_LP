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

fun teval (e:expr) (env: plcType env) : plcType =
	case e of
		  ConI _ => IntT
		| Var x => lookup env x
		| ConB _ => BoolT
		| List [] => ListT []
		| ESeq(SeqT t) => SeqT t
	
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

					| ("<", IntT, IntT)	=> t1
					| ("<", _, _) => raise NotEqTypes
					
					| ("<=", IntT, IntT) => t1
					| ("<=", _, _) => raise NotEqTypes

					| ("=", IntT, IntT) => t1
					| ("=", BoolT, BoolT) => t1
					| ("=", SeqT x1, SeqT x2) => t1
					| ("=", _, _) => raise NotEqTypes

					| (";" , _ , _) => t2
					
					| ("&&", BoolT, BoolT)  => t1
					| ("&&", _, _) => raise NotEqTypes

					(*verificar*)
					| ("::", SeqT x1, SeqT x2) => if x1 = x2 then SeqT x1 else raise NotEqTypes
					(*| ("::", SeqT x1, ESeq(SeqT x2)) => if x2 = SeqT x1 then SeqT x1 else raise NotEqTypes*)
					| ("::", _, _) => raise UnknownType



					| _   =>  raise UnknownType

					
				end
				
		| Let(x, e1, e2) =>
				let
					val t = teval e1 env
					val env' = (x,t)::env
				in
					teval e2 env'
				end

		
		


		| _   =>  raise UnknownType
	
	val expr0 = Prim2("+", ConI 12, ConI 11);

	teval expr0 [];

