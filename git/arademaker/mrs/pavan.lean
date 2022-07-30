
/-
2. Some of us are more interested in football than basketball
3. Michael Jordan's birth place is Brooklyn, New York 
4. Michael Jordan was not born in North Carolina
5. Donald Trump is the president of the United States
6. Joe Biden is the president of the United States
7. All presidents are politicians
8. Some politicians are presidents
9. Donald Trump is a businessman
10. Donald Trump is not a politician 
11. If people fall they might get hurt
12. Knives are used to cut vegetables
13. Donald John Trump (born June 14, 1946) is an American politician, media personality, and businessman who served as the 45th president of the United States from 2017 to 2021.
14. Sport pertains to any form of competitive physical activity or game that aims to use, maintain, or improve physical ability and skills while providing enjoyment to participants and, in some cases, entertainment to spectators.
15. American football, also referred to simply as football in the United States and Canada, and also known as gridiron, is a team sport played by two teams of eleven players on a rectangular field with goalposts at each end.
-/


/- All people who go to Apple Store buy electronics

[ TOP: h0
  INDEX: e2
  RELS: < [ _all_q<0:3>             LBL: h4 ARG0: x3 RSTR: h5 BODY: h6 ]
          [ _people_n_of<4:10>      LBL: h7 ARG0: x3 ARG1: i8 ]
          [ _go_v_1<15:17>          LBL: h7 ARG0: e9 ARG1: x3 ]
          [ _to_p_dir<18:20>        LBL: h7 ARG0: e10 ARG1: e9 ARG2: x11 ]
          [ proper_q<21:32>         LBL: h12 ARG0: x11 RSTR: h13 BODY: h14 ]
          [ compound<21:32>         LBL: h15 ARG0: e16 ARG1: x11 ARG2: x17 ]
          [ proper_q<21:26>         LBL: h18 ARG0: x17 RSTR: h19 BODY: h20 ]
          [ named<21:26>            LBL: h21 ARG0: x17 CARG: "Apple" ]
          [ named<27:32>            LBL: h15 ARG0: x11 CARG: "Store" ]
          [ _buy_v_1<33:36>         LBL: h1 ARG0: e2 ARG1: x3 ARG2: x24 ]
          [ udef_q<37:48>           LBL: h25 ARG0: x24 RSTR: h26 BODY: h27 ]
          [ _electronics_n_1<37:48> LBL: h28 ARG0: x24 ] >
  HCONS: < h0 qeq h1 h5 qeq h7 h13 qeq h15 h19 qeq h21 h26 qeq h28 > ]


(b / buy-01
      :ARG0 (p / person
            :ARG0-of (g / go-02
                  :ARG4 (s / store
                        :name (n / name
                              :op1 "Apple"
                              :op2 "Store")))
            :mod (a / all))
      :ARG1 (e / electronics))
-/

section 
 constant u : Type
 constant named : u → String → Prop
 constant compound : u → u → u → Prop
 constant _electronics_n_1 : u → Prop
 constant _people_n_of : u → u → Prop
 constant _go_v_1 : u → u → Prop
 constant _to_p_dir : u → u → u → Prop
 constant _buy_v_1 : u → u → u → Prop

 constant store : u → Prop
 constant person : u → Prop
 constant electronics : u → Prop
 constant buy_01 : u → Prop
 constant go_02 : u → Prop
 constant ARG0 : u → u → Prop
 constant ARG0_of : u → u → Prop
 constant ARG1 : u → u → Prop
 constant ARG4 : u → u → Prop
 constant ALL : u → Prop
 constant mod : u → u → Prop
 constant name : u → Prop
 constant name1 : u → u → Prop
 constant op1 : u → String → Prop
 constant op2 : u → String → Prop
  
 -- amr2logic 
 axiom a0 : ∃ b, (buy_01 b ∧ ∃ p, (person p ∧ ∃ g, (go_02 g ∧ ∃ s, (store s ∧ ∃ n, (name n ∧ op1 n "Apple" ∧ op2 n "Store" ∧ name1 s n) 
  ∧ ARG4 g s ) ∧ ARG0_of p g) ∧ ∃ a, (ALL a ∧ mod p a) ∧ ARG0 b p) ∧ ∃ e,(electronics e ∧ ARG1 b e))

 -- MRS2logic 
 axiom a1 : ∃ e2, ∃ i8, ∃ e9, ∃ e10, ∃ e16, ∃ x11, (∃ x17, named x17 "Apple" ∧ compound e16 x11 x17 ∧ named x11 "Store") 
  ∧ (∃ x24, _electronics_n_1 x24 ∧ (∀ x3, (_people_n_of x3 i8 ∧ _go_v_1 e9 x3 ∧ _to_p_dir e10 e9 x11) → _buy_v_1 e2 x3 x24))

 -- MRS+AMR manually simplified
 axiom a2 : ∃ e2 i8 e9 e10 x11 x24, named x11 "Apple Store" ∧ store x11 ∧ _electronics_n_1 x24 
  ∧ (∀ x3, (_people_n_of x3 i8 ∧ _go_v_1 e9 x3 ∧ _to_p_dir e10 e9 x11) → _buy_v_1 e2 x3 x24)

end 


