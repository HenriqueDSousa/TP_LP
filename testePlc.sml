use "Plc.sml";


val e = fromString "fun rec f1(Int x):Int = x + 1; f1(12)";
run e;

val expr0 = Prim2("+", ConI 2, ConI 3);
val expr1 = Prim2("-", ConI 2, ConI 3);
val expr2 = Prim2("/", ConI 6, ConI 3);
val expr3 = Prim2("*", ConI 2, ConI 3);
val expr4 = List([ConI 6, ConB false]);
val expr5 = Item(1, List([ConI 6, ConB false]));
val expr6 = ESeq(SeqT BoolT);
val expr7 = Prim1("print", ConI 27);
val expr8 = Prim2 ("::", ConI 3, Prim2 ("::", ConI 4, Prim2 ("::", ConI 5, ESeq (SeqT IntT))));
val expr9 = Prim2 (";", Prim1 ("print", ConI 27), ConB true);
val expr10 = Anon (IntT, "x", Prim1("-", Var "x"));
val expr11 = Let("x", ConI 9, Prim2 ("+", Var "x", ConI 1));
val expr12 = Let("f", Anon (IntT, "x", Var "x"), Call (Var "f", ConI 5));
val expr13 = If(ConB true, ConI 1, ConI 2);
val expr14 = Match(Var "x", [(SOME (ConI 0), ConI 1), (SOME (ConI 1), ConI 2),(NONE, Prim1("-", ConI 1))]);
val expr15 = Prim2("&&", ConB true, ConB false);
val expr16 = Prim2("&&", ConB true, Prim2("&&", ConB true, ConB true));
val expr17 = Letrec
      ("f",IntT,"x",IntT,
       If
         (Prim2 ("<=",Var "x",ConI 0),ConI 0,
          Prim2 ("+",Var "x",Call (Var "f",Prim2 ("-",Var "x",ConI 1)))),
       Call (Var "f",ConI 5));
val expr18 = Prim1("!", ConB true);
val expr19 = Prim1("hd", expr8);
val expr20 = Prim1("tl", expr8);
val expr21 = Prim1("ise", expr8);
val expr22 = Prim1("ise", expr6);
val expr23 = Match (Var "x",[]);
val expr24 = Match (Var "x",[(SOME (ConB false), ConI 1), (NONE, Prim1 ("-",ConI 1))]);
val expr25 = Match (ConI 5,[(SOME (ConI 0), ConI 1), (SOME (ConI 1), ConI 2)]);
val expr26 = Prim2("=", List [ConI 1,ConB false,List []],List [ConI 1,ConB false,List []]);
val expr27 = Prim2("=", List [ConI 1,ConB true,List []],List [ConI 1,ConB false,List []]);
val expr28 = Prim2("=", Prim2 ("::", ConI 2, Prim2 ("::", ConI 4, Prim2 ("::", ConI 5, ESeq (SeqT IntT)))), Prim2 ("::", ConI 3, Prim2 ("::", ConI 4, Prim2 ("::", ConI 5, ESeq (SeqT IntT)))));
val expr29 = Prim2("=", Prim2 ("::", ConI 3, Prim2 ("::", ConI 4, Prim2 ("::", ConI 5, ESeq (SeqT IntT)))), Prim2 ("::", ConI 3, Prim2 ("::", ConI 4, Prim2 ("::", ConI 5, ESeq (SeqT IntT)))));
val expr30 = Prim2 ("=",List [ConI 1,Anon (IntT,"x",Var "x"),List []], List [ConI 1,Anon (IntT,"x",Var "x"),List []]);
val expr31 = Prim2
    ("=",
     Prim2
       ("::",List [Anon (IntT,"x",Var "x"),ConI 2],
        Prim2 ("::",List [ConI 3,ConI 4],ESeq (SeqT (ListT [IntT, IntT])))),
     Prim2
       ("::",List [Anon (IntT,"x",Var "x"),ConI 2],
        Prim2 ("::",List [ConI 3,ConI 4],ESeq ((ListT [IntT, IntT])))));
val expr32 = Prim2("+", ConB false, ConI 29);
val expr33 = Let ("f", Anon (IntT, "x", 
                Let ("g",Anon (IntT,"y",
                    Prim2 ("+",Var "x",Var "y")),Var "g")),
            Call (Call (Var "f",ConI 3),ConI 4));
val expr34 = Item(0, List([ConI 6, ConB false]));
val expr35 = Item(3, List([ConI 6, ConB false]));
val expr36 = Let ("f",Anon (IntT, "x",Var "x"),Var "f");
val expr37 =Let("E",
            ESeq (SeqT IntT), 
            Let ("reverse",
                Anon(SeqT IntT,"s", 
                    Letrec("rev", ListT [SeqT IntT, SeqT IntT],"$list",SeqT IntT, Let ("s1",Item (1,Var "$list"),Let("s2",Item (2,Var "$list"), Match (Var "s1",[(SOME (Var "E"), Var "s2"), (NONE,Let("h",Prim1 ("hd",Var "s1"), Let ("t",Prim1 ("tl",Var "s1"),Call(Var "rev", List [Var "t", Prim2 ("::",Var "h",Var "s2")]))))]))), 
                    Call (Var "rev",List [Var "s", Var "E"]))),
                Call 
                (Var "reverse", Prim2 ("::",ConI 1,Prim2 ("::",ConI 2,Prim2 ("::",ConI 3,Var "E"))))
                )
            );
val expr38 = Let ("p",List [ConI 1, ConI 3], Let ("f", 
Anon (ListT [IntT, IntT], "$list", 
    Let ("x",Item (1, Var "$list"), Let ("y",Item (2, Var "$list"),
    Prim2 ("-",Var "x",Var "y")))),
    Call (Var "f",Var "p")));

val expr39 = (Let ("E", ESeq (SeqT IntT), 
                Let ("reverse", 
                Anon (SeqT IntT, "l",
                    Letrec (
                        "rev",
                        ListT [SeqT IntT, SeqT IntT],
                        "$list", 
                        SeqT IntT, 
                        Let ("l1", 
                            Item (1, Var "$list"),
                            Let ("l2",
                                Item (2, Var "$list"), 
                                If (Prim1 ("ise",Var "l1"), 
                                    Var "l2",Call (Var "rev",
                                                    List [Prim1 ("tl",Var "l1"),
                                                        Prim2 ("::", Prim1 ("hd",Var "l1"),
                                                        Var "l2")])))),
                        Call (Var "rev", List [Var "l", Var "E"]))),
                    Call (Var "reverse", Prim2 ("::",ConI 1,Prim2 ("::",ConI 2,Prim2 ("::",ConI 3,Var "E")))))));

run expr0;
run expr1;
run expr2;
run expr0;
run expr3;
run expr4;
run expr5;
run expr6;
run expr7;
run expr8;
run expr9;
run expr10;
run expr11;
run expr12;
run expr13;
run expr14;
run expr14;
run expr14;
run expr15;
run expr16;
run expr17; 
run expr18;
run expr19;
run expr20;
run expr21;
run expr22;
run expr23;
run expr24;
run expr25;
run expr26;
run expr27;
run expr28;
run expr29;
run expr30;
run expr31;
run expr32;
run expr33;
run expr34;
run expr35;
run expr36;
run expr37;
run expr38;
run expr39;
