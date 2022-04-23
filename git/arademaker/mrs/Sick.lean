
-- The young boys are playing outdoors and the man is smiling nearby    
-- The kids are playing outdoors near a man with a smile     
-- ENTAILMENT

/-
SENT: The young boys are playing outdoors and the man is smiling nearby

<
h1,e3:PROP:PRES:INDICATIVE:+:-,{
h4:_the_q<0:3>(x7:3:PL:+, h6, h5),
h8:_young_a_1<4:9>(e9:PROP:UNTENSED:INDICATIVE:BOOL:-, x7),
h8:_boy_n_1<10:14>(x7),
h2:_play_v_1<19:26>(e10:PROP:PRES:INDICATIVE:+:-, x7, i11),
h2:loc_nonsp<27:35>(e12:PROP:UNTENSED:INDICATIVE:-:-, e10, x13:3:SG),
h14:place_n<27:35>(x13),
h15:def_implicit_q<27:35>(x13, h16, h17),
h14:_outdoors_a_1<27:35>(e18:PROP:UNTENSED:INDICATIVE:-:-, x13),
h2:_and_c<36:39>(e3, e10, e19:PROP:PRES:INDICATIVE:+:-),
h20:_the_q<40:43>(x23:3:SG, h22, h21),h24:_man_n_1<44:47>(x23),
h2:_smile_v_1<51:58>(e19, x23, i25),
h2:_nearby_p<59:65>(e26:PROP:UNTENSED:INDICATIVE:-:-, e19)},
{h1 qeq h2,h6 qeq h8,h16 qeq h14,h22 qeq h24}
>

_the_q(x7, _young_a_1(e9, x7) /\ _boy_n_1(x7), 
	   def_implicit_q(x13, 
			  place_n(x13) /\ _outdoors_a_1(e18, x13),
			  _the_q(x23, _man_n_1(x23),
				      _play_v_1(e10, x7, i11) /\
				      loc_nonsp(e12, e10, x13) /\
				      _and_c(e3, e10, e19) /\
				      _smile_v_1(e19, x23, i25) /\
				      _nearby_p(e26, e19))))


SENT: The kids are playing outdoors near a man with a smile

<
h1,e3:PROP:PRES:INDICATIVE:+:-,{
h4:_the_q<0:3>(x7:3:PL:+, h6, h5),
h8:_kid_n_1<4:8>(x7),
h2:_play_v_1<13:20>(e3, x7, i9),
h2:loc_nonsp<21:29>(e10:PROP:UNTENSED:INDICATIVE:-:-, e3, x11:3:SG),
h12:place_n<21:29>(x11),
h13:def_implicit_q<21:29>(x11, h14, h15),
h12:_outdoors_a_1<21:29>(e16:PROP:UNTENSED:INDICATIVE:-:-, x11),
h2:_near_p_state<30:34>(e17:PROP:UNTENSED:INDICATIVE:-:-, e3, x18:3:SG:+),
h19:_a_q<35:36>(x18, h21, h20),
h22:_man_n_1<37:40>(x18),
h22:_with_p<41:45>(e23:PROP:UNTENSED:INDICATIVE:-:-, x18, x24:3:SG:+),
h25:_a_q<46:47>(x24, h27, h26),
h28:_smile_n_1<48:53>(x24)},
{h1 qeq h2,h6 qeq h8,h14 qeq h12,h21 qeq h22,h27 qeq h28}>

_the_q(x7, _kid_n_1(x7),
	   def_implicit_q(x11, place_n(x11) /\ _outdoors_a_1(e16, x11),
			       _a_q(x18, _a_q(x24, _smile_n_1(x24),
						   _man_n_1(x18) /\
						   _with_p(e23, x18, x24)),
					 _play_v_1(e3, x7, i9) /\
					 loc_nonsp(e10, e3, x11) /\
					 _near_p_state(e17, e3, x18))))

-/


section 
 
 constant x : Type
 constant e : Type 
 constant i : Type 
 constant h : Type
 constant _young_a_1 : e → x → Prop
 constant _boy_n_1 : x → Prop
 constant _kid_n_1 : x → Prop
 constant _smile_n_1 : x → Prop 
 constant _man_n_1 : x → Prop
 constant place_n : x → Prop
 constant _outdoors_a_1 : e → x → Prop
 constant _play_v_1 : e → x → i → Prop
 constant loc_nonsp : e → e → x → Prop
 constant _smile_v_1 : e → x → i → Prop
 constant _nearby_p : e → e → Prop
 constant _and_c : e → e → e → Prop
 constant _with_p : e → x → x → Prop
 constant _near_p_state : e → e → x → Prop

 def h₁ : Prop := ∃ i11 i25 e10 e26 e12 e3 e19 e9 e18, 
  ∃ x7, (_young_a_1 e9 x7 ∧ _boy_n_1 x7) ∧ 
   (∃ x13, (place_n x13 ∧ _outdoors_a_1 e18 x13) ∧ 
    (∃ x23, _man_n_1 x23 ∧ 
            (_play_v_1 e10 x7 i11 ∧ loc_nonsp e12 e10 x13 ∧ _and_c e3 e10 e19 ∧ _smile_v_1 e19 x23 i25 ∧ _nearby_p e26 e19)))

 def h₂ : Prop := ∃ i9 e3 e23 e16 e10 e17, 
  ∃ x7, _kid_n_1 x7 ∧ 
   (∃ x11, (place_n x11 ∧ _outdoors_a_1 e16 x11) ∧ 
    (∃ x18, (∃ x24, _smile_n_1 x24 ∧ _man_n_1 x18 ∧ _with_p e23 x18 x24) ∧ (_play_v_1 e3 x7 i9 ∧ loc_nonsp e10 e3 x11 ∧ _near_p_state e17 e3 x18)))

theorem my : h₁ → h₂ := by 
 unfold h₁
 unfold h₂
 intro h
 
 
end
