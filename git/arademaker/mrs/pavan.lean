
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

ERG/ACE

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

amr parser

 (b / buy-01
      :ARG0 (p / person
            :ARG0-of (g / go-02
                  :ARG4 (s / store
                        :name (n / name
                              :op1 "Apple"
                              :op2 "Store")))
            :mod (a / all))
      :ARG1 (e / electronics))

amr2logic

 exists b.(buy_01(b) & exists p.(person(p) & exists g.(go_02(g) & exists s.(store(s) 
  & exists n.(name(n) & op1(n,"Apple") & op2(n,"Store") & name(s,n)) & ARG4(g,s)) & ARG0_of(p,g)) 
  & exists a.(ALL(a) & mod(p,a)) & ARG0(b,p)) & exists e.(electronics(e) & ARG1(b,e)))
-/

section 
 opaque u : Type

 -- constants from MRS
 opaque named : u → String → Prop
 opaque neg : u → Prop → Prop
 opaque compound : u → u → u → Prop
 opaque _electronics_n_1 : u → Prop
 opaque _people_n_of : u → u → Prop
 opaque _go_v_1 : u → u → Prop
 opaque _to_p_dir : u → u → u → Prop
 opaque _in_p_state : u → u → u → Prop
 opaque _buy_v_1 : u → u → u → Prop
 opaque _bear_v_2 : u → u → u → Prop

 -- constants from AMR
 opaque store : u → Prop
 opaque person : u → Prop
 opaque electronics : u → Prop
 opaque buy_01 : u → Prop
 opaque go_02 : u → Prop
 opaque ARG0 : u → u → Prop
 opaque ARG0_of : u → u → Prop
 opaque ARG1 : u → u → Prop
 opaque ARG4 : u → u → Prop
 opaque ALL : u → Prop
 opaque mod : u → u → Prop
 opaque name : u → Prop
 opaque name1 : u → u → Prop
 opaque op1 : u → String → Prop
 opaque op2 : u → String → Prop

 -- mappings
 def s1 := ∀ e, buy_01 e ↔ ∃ x y,_buy_v_1 e x y
 def s2 := ∀ e, go_02 e ↔ ∃ x,_go_v_1 e x
 def s3 := electronics = _electronics_n_1  

 -- amr2logic 
 def a10 := ∃ b, (buy_01 b ∧ ∃ p, (person p ∧ ∃ g, (go_02 g ∧ ∃ s, (store s 
  ∧ ∃ n, (name n ∧ op1 n "Apple" ∧ op2 n "Store" ∧ name1 s n) 
  ∧ ARG4 g s ) ∧ ARG0_of p g) ∧ ∃ a, (ALL a ∧ mod p a) ∧ ARG0 b p) ∧ ∃ e,(electronics e ∧ ARG1 b e))

 -- mrs2logic 
 def a11 := ∃ e2, ∃ i8, ∃ e9, ∃ e10, ∃ e16, ∃ x11, (∃ x17, named x17 "Apple" ∧ compound e16 x11 x17 ∧ named x11 "Store") 
  ∧ (∃ x24, _electronics_n_1 x24 ∧ (∀ x3, (_people_n_of x3 i8 ∧ _go_v_1 e9 x3 ∧ _to_p_dir e10 e9 x11) → _buy_v_1 e2 x3 x24))

 -- MRS+AMR manually simplified
 def a12 := ∃ e2 i8 e9 e10 x11 x24, named x11 "Apple Store" ∧ store x11 ∧ _electronics_n_1 x24 
  ∧ (∀ x3, (_people_n_of x3 i8 ∧ _go_v_1 e9 x3 ∧ _to_p_dir e10 e9 x11) → _buy_v_1 e2 x3 x24)

 -- prenex normal form
 def a13 := ∃ e2 i8 e9 e10 x11 x24, ∀ x3, named x11 "Apple Store" ∧ store x11 ∧ _electronics_n_1 x24 
   ∧ (_people_n_of x3 i8 ∧ _go_v_1 e9 x3 ∧ _to_p_dir e10 e9 x11 → _buy_v_1 e2 x3 x24)

 -- prenex conjunctive normal form
 def a14 := ∃ e2 i8 e9 e10 x11 x24, ∀ x3, 
   (named x11 "Apple Store" ∧ store x11 ∧ _electronics_n_1 x24 
   ∧ (¬_people_n_of x3 i8 ∨ ¬ _go_v_1 e9 x3 ∨ ¬_to_p_dir e10 e9 x11 ∨ _buy_v_1 e2 x3 x24)) 


 theorem t1 : a12 ↔ a13 := by 
  unfold a12, a13
  apply Iff.intro
  case mp =>
   intro ⟨a, b, c, d, e, f, ha, hs, he, hr⟩
   exact ⟨a, b, c, d, e, f, λ x => ⟨ha, hs, he, hr x⟩⟩ 
  case mpr =>
   intro ⟨a, b, c, d, e, f, pa⟩
   have ⟨ha, hs, he, _⟩ := pa a
   exact ⟨a, b, c, d, e, f, ha, hs, he, λ x => (pa x).2.2.2⟩



 -- alternative proof of t1 above using more automation
 -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20FOL.20reasoning.20in.20Lean4

 @[simp]
 theorem and_exists (p : Prop) (q : α → Prop) : p ∧ (∃ a, q a) ↔ ∃ a, p ∧ q a := by
  apply Iff.intro
  case mp =>
    intro ⟨a, b, c⟩
    exact ⟨b, a, c⟩
  case mpr =>
    intro ⟨a, b, c⟩
    exact ⟨b, a, c⟩

 @[simp]
 theorem and_forall [Nonempty α] (p) (q : α → Prop) : p ∧ (∀ a, q a) ↔ ∀ a, p ∧ q a := by
  apply Iff.intro
  case mp =>
    intro ⟨a, b⟩ c
    exact ⟨a, b c⟩
  case mpr =>
    intro a
    refine ⟨(a Classical.ofNonempty).1, ?_⟩
    intro b
    exact (a b).2

 axiom u.nonempty : Nonempty u
 instance : Nonempty u := u.nonempty

 theorem t1' : a12 ↔ a13 := by 
   simp [a12, a13]


 theorem t2 : a2 ↔ a22 := by
  unfold a2, a22
  apply Iff.intro
  case mp =>
   intro ⟨a, b, c, d, e, f, ha, hs, he, hr⟩
   exists a; exists b; exists c; exists d; exists e; exists f
   intro g; have hg := hr g
   apply And.intro; exact ha
   apply And.intro; exact hs
   apply And.intro; exact he
   sorry  -- need to finish
   

/-
[ TOP: h0
  INDEX: e2
  RELS: < [ proper_q<0:14>     LBL: h4  ARG0: x3 RSTR: h5 BODY: h6 ]
          [ compound<0:14>     LBL: h7  ARG0: e8 ARG1: x3 ARG2: x9 ]
          [ proper_q<0:7>      LBL: h10 ARG0: x9 RSTR: h11 BODY: h12 ]
          [ named<0:7>         LBL: h13 ARG0: x9 CARG: "Michael" ]
          [ named<8:14>        LBL: h7  ARG0: x3 CARG: "Jordan" ]
          [ neg<19:22>         LBL: h1  ARG0: e16 ARG1: h17 ]
          [ _bear_v_2<23:27>   LBL: h18 ARG0: e2 ARG1: u19 ARG2: x3 ]
          [ _in_p_state<28:30> LBL: h18 ARG0: e20 ARG1: e2 ARG2: x21 ]
          [ proper_q<31:46>    LBL: h22 ARG0: x21 RSTR: h23 BODY: h24 ]
          [ compound<31:46>    LBL: h25 ARG0: e26 ARG1: x21 ARG2: x27 ]
          [ proper_q<31:36>    LBL: h28 ARG0: x27 RSTR: h29 BODY: h30 ]
          [ named<31:36>       LBL: h31 ARG0: x27 CARG: "North" ]
          [ named<37:45>       LBL: h25 ARG0: x21 CARG: "Carolina" ] >
  HCONS: < h0 qeq h1 h5 qeq h7 h11 qeq h13 h17 qeq h18 h23 qeq h25 h29 qeq h31 >
  ICONS: < e2 topic x3 > ]
-/
 
def a20 := ∃ e2 e8 e16 u19 e20 e26 x9, named x9 "Michael" 
            ∧ neg e16 (∃ x21, 
                        (∃ x27, named x27 "North" ∧ compound e26 x21 x27 ∧ named x21 "Carolina") 
                         ∧ (∃ x3, (compound e8 x3 x9 ∧ named x3 "Jordan") ∧ _bear_v_2 e2 u19 x3 ∧ _in_p_state e20 e2 x21))


-- simplified alternative after combining all NN compounds into a
-- single entity. Can it be done automatically?

def a21 := ∃ e2 e16 u19 e20, neg e16 (∃ x21, 
                             (named x21 "North Carolina") 
                             ∧ (∃ x3, (named x3 "Michael Jordan") ∧ _bear_v_2 e2 u19 x3 ∧ _in_p_state e20 e2 x21))

end
