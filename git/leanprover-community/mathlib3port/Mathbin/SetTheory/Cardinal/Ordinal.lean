/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathbin.Order.Bounded
import Mathbin.SetTheory.Ordinal.Principal
import Mathbin.Tactic.Linarith.Default

/-!
# Cardinals and ordinals

Relationships between cardinals and ordinals, properties of cardinals that are proved
using ordinals.

## Main definitions

* The function `cardinal.aleph'` gives the cardinals listed by their ordinal
  index, and is the inverse of `cardinal.aleph_idx`.
  `aleph' n = n`, `aleph' ω = cardinal.omega = ℵ₀`, `aleph' (ω + 1) = ℵ₁`, etc.
  It is an order isomorphism between ordinals and cardinals.
* The function `cardinal.aleph` gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = cardinal.omega = ℵ₀`, `aleph 1 = ℵ₁` is the first
  uncountable cardinal, and so on.

## Main Statements

* `cardinal.mul_eq_max` and `cardinal.add_eq_max` state that the product (resp. sum) of two infinite
  cardinals is just their maximum. Several variations around this fact are also given.
* `cardinal.mk_list_eq_mk` : when `α` is infinite, `α` and `list α` have the same cardinality.
* simp lemmas for inequalities between `bit0 a` and `bit1 b` are registered, making `simp`
  able to prove inequalities about numeral cardinals.

## Tags

cardinal arithmetic (for infinite cardinals)
-/


noncomputable section

open Function Cardinal Set Equivₓ

open Classical Cardinal

universe u v w

namespace Cardinal

section UsingOrdinals

open Ordinal

theorem ord_is_limit {c} (co : ω ≤ c) : (ord c).IsLimit := by
  refine' ⟨fun h => omega_ne_zero _, fun a => lt_imp_lt_of_le_imp_le _⟩
  · rw [← Ordinal.le_zero, ord_le] at h
    simpa only [card_zero, nonpos_iff_eq_zero] using le_transₓ co h
    
  · intro h
    rw [ord_le] at h⊢
    rwa [← @add_one_of_omega_le (card a), ← card_succ]
    rw [← ord_le, ← le_succ_of_is_limit, ord_le]
    · exact le_transₓ co h
      
    · rw [ord_omega]
      exact omega_is_limit
      
    

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this definition, we register additionally that this function is an initial segment,
  i.e., it is order preserving and its range is an initial segment of the ordinals.
  For the basic function version, see `aleph_idx`.
  For an upgraded version stating that the range is everything, see `aleph_idx.rel_iso`. -/
def AlephIdx.initialSeg : @InitialSeg Cardinal Ordinal (· < ·) (· < ·) :=
  @RelEmbedding.collapse Cardinal Ordinal (· < ·) (· < ·) _ Cardinal.ord.orderEmbedding.ltEmbedding

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  For an upgraded version stating that the range is everything, see `aleph_idx.rel_iso`. -/
def alephIdx : Cardinal → Ordinal :=
  aleph_idx.initial_seg

@[simp]
theorem alephIdx.initial_seg_coe : (AlephIdx.initialSeg : Cardinal → Ordinal) = aleph_idx :=
  rfl

@[simp]
theorem aleph_idx_lt {a b} : alephIdx a < alephIdx b ↔ a < b :=
  AlephIdx.initialSeg.toRelEmbedding.map_rel_iff

@[simp]
theorem aleph_idx_le {a b} : alephIdx a ≤ alephIdx b ↔ a ≤ b := by
  rw [← not_ltₓ, ← not_ltₓ, aleph_idx_lt]

theorem alephIdx.init {a b} : b < alephIdx a → ∃ c, alephIdx c = b :=
  AlephIdx.initialSeg.init _ _

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this version, we register additionally that this function is an order isomorphism
  between cardinals and ordinals.
  For the basic function version, see `aleph_idx`. -/
def alephIdx.relIso : @RelIso Cardinal.{u} Ordinal.{u} (· < ·) (· < ·) :=
  @RelIso.ofSurjective Cardinal.{u} Ordinal.{u} (· < ·) (· < ·) AlephIdx.initialSeg.{u} <|
    (InitialSeg.eq_or_principal AlephIdx.initialSeg.{u}).resolve_right fun ⟨o, e⟩ => by
      have : ∀ c, aleph_idx c < o := fun c => (e _).2 ⟨_, rfl⟩
      refine' Ordinal.induction_on o _ this
      intro α r _ h
      let s := sup.{u, u} fun a : α => inv_fun aleph_idx (Ordinal.typein r a)
      apply not_le_of_gtₓ (lt_succ_self s)
      have I : injective aleph_idx := aleph_idx.initial_seg.to_embedding.injective
      simpa only [typein_enum, left_inverse_inv_fun I (succ s)] using
        le_sup.{u, u} (fun a => inv_fun aleph_idx (Ordinal.typein r a)) (Ordinal.enum r _ (h (succ s)))

@[simp]
theorem alephIdx.rel_iso_coe : (alephIdx.relIso : Cardinal → Ordinal) = aleph_idx :=
  rfl

@[simp]
theorem type_cardinal : @Ordinal.type Cardinal (· < ·) _ = Ordinal.univ.{u, u + 1} := by
  rw [Ordinal.univ_id] <;> exact Quotientₓ.sound ⟨aleph_idx.rel_iso⟩

@[simp]
theorem mk_cardinal : # Cardinal = univ.{u, u + 1} := by
  simpa only [card_type, card_univ] using congr_argₓ card type_cardinal

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = ℵ₁`, etc.
  In this version, we register additionally that this function is an order isomorphism
  between ordinals and cardinals.
  For the basic function version, see `aleph'`. -/
def Aleph'.relIso :=
  Cardinal.alephIdx.relIso.symm

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = ℵ₁`, etc. -/
def aleph' : Ordinal → Cardinal :=
  aleph'.rel_iso

@[simp]
theorem aleph'.rel_iso_coe : (Aleph'.relIso : Ordinal → Cardinal) = aleph' :=
  rfl

@[simp]
theorem aleph'_lt {o₁ o₂ : Ordinal.{u}} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ :=
  Aleph'.relIso.map_rel_iff

@[simp]
theorem aleph'_le {o₁ o₂ : Ordinal.{u}} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ :=
  le_iff_le_iff_lt_iff_lt.2 aleph'_lt

@[simp]
theorem aleph'_aleph_idx (c : Cardinal.{u}) : aleph' c.alephIdx = c :=
  Cardinal.alephIdx.relIso.toEquiv.symm_apply_apply c

@[simp]
theorem aleph_idx_aleph' (o : Ordinal.{u}) : (aleph' o).alephIdx = o :=
  Cardinal.alephIdx.relIso.toEquiv.apply_symm_apply o

@[simp]
theorem aleph'_zero : aleph' 0 = 0 := by
  rw [← nonpos_iff_eq_zero, ← aleph'_aleph_idx 0, aleph'_le] <;> apply Ordinal.zero_le

@[simp]
theorem aleph'_succ {o : Ordinal.{u}} : aleph' o.succ = (aleph' o).succ :=
  le_antisymmₓ
    (Cardinal.aleph_idx_le.1 <| by
      rw [aleph_idx_aleph', Ordinal.succ_le, ← aleph'_lt, aleph'_aleph_idx] <;> apply Cardinal.lt_succ_self)
    (Cardinal.succ_le.2 <| aleph'_lt.2 <| Ordinal.lt_succ_self _)

@[simp]
theorem aleph'_nat : ∀ n : ℕ, aleph' n = n
  | 0 => aleph'_zero
  | n + 1 =>
    show aleph' (Ordinal.succ n) = n.succ by
      rw [aleph'_succ, aleph'_nat, nat_succ]

theorem aleph'_le_of_limit {o : Ordinal.{u}} (l : o.IsLimit) {c} : aleph' o ≤ c ↔ ∀, ∀ o' < o, ∀, aleph' o' ≤ c :=
  ⟨fun h o' h' => le_transₓ (aleph'_le.2 <| le_of_ltₓ h') h, fun h => by
    rw [← aleph'_aleph_idx c, aleph'_le, Ordinal.limit_le l]
    intro x h'
    rw [← aleph'_le, aleph'_aleph_idx]
    exact h _ h'⟩

@[simp]
theorem aleph'_omega : aleph' Ordinal.omega = ω :=
  eq_of_forall_ge_iff fun c => by
    simp only [aleph'_le_of_limit omega_is_limit, Ordinal.lt_omega, exists_imp_distrib, omega_le]
    exact
      forall_swap.trans
        (forall_congrₓ fun n => by
          simp only [forall_eq, aleph'_nat])

/-- `aleph'` and `aleph_idx` form an equivalence between `ordinal` and `cardinal` -/
@[simp]
def aleph'Equiv : Ordinal ≃ Cardinal :=
  ⟨aleph', alephIdx, aleph_idx_aleph', aleph'_aleph_idx⟩

/-- The `aleph` function gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ω`, `aleph 1 = succ ω` is the first
  uncountable cardinal, and so on. -/
def aleph (o : Ordinal) : Cardinal :=
  aleph' (Ordinal.omega + o)

@[simp]
theorem aleph_lt {o₁ o₂ : Ordinal.{u}} : aleph o₁ < aleph o₂ ↔ o₁ < o₂ :=
  aleph'_lt.trans (add_lt_add_iff_left _)

@[simp]
theorem aleph_le {o₁ o₂ : Ordinal.{u}} : aleph o₁ ≤ aleph o₂ ↔ o₁ ≤ o₂ :=
  le_iff_le_iff_lt_iff_lt.2 aleph_lt

@[simp]
theorem max_aleph_eq (o₁ o₂ : Ordinal) : max (aleph o₁) (aleph o₂) = aleph (max o₁ o₂) := by
  cases' le_totalₓ (aleph o₁) (aleph o₂) with h h
  · rw [max_eq_rightₓ h, max_eq_rightₓ (aleph_le.1 h)]
    
  · rw [max_eq_leftₓ h, max_eq_leftₓ (aleph_le.1 h)]
    

@[simp]
theorem aleph_succ {o : Ordinal.{u}} : aleph o.succ = (aleph o).succ := by
  rw [aleph, Ordinal.add_succ, aleph'_succ] <;> rfl

@[simp]
theorem aleph_zero : aleph 0 = ω := by
  simp only [aleph, add_zeroₓ, aleph'_omega]

theorem omega_le_aleph' {o : Ordinal} : ω ≤ aleph' o ↔ Ordinal.omega ≤ o := by
  rw [← aleph'_omega, aleph'_le]

theorem omega_le_aleph (o : Ordinal) : ω ≤ aleph o := by
  rw [aleph, omega_le_aleph'] <;> apply Ordinal.le_add_right

theorem aleph'_pos {o : Ordinal} (ho : 0 < o) : 0 < aleph' o := by
  rwa [← aleph'_zero, aleph'_lt]

theorem aleph_pos (o : Ordinal) : 0 < aleph o :=
  omega_pos.trans_le (omega_le_aleph o)

instance (o : Ordinal) : Nonempty (aleph o).ord.out.α := by
  rw [out_nonempty_iff_ne_zero, ← ord_zero]
  exact fun h => (ord_injective h).not_gt (aleph_pos o)

theorem ord_aleph_is_limit (o : Ordinal) : IsLimit (aleph o).ord :=
  ord_is_limit <| omega_le_aleph _

instance (o : Ordinal) : NoMaxOrder (aleph o).ord.out.α :=
  Ordinal.out_no_max_of_succ_lt (ord_aleph_is_limit o).2

theorem exists_aleph {c : Cardinal} : ω ≤ c ↔ ∃ o, c = aleph o :=
  ⟨fun h =>
    ⟨alephIdx c - Ordinal.omega, by
      rw [aleph, Ordinal.add_sub_cancel_of_le, aleph'_aleph_idx] <;> rwa [← omega_le_aleph', aleph'_aleph_idx]⟩,
    fun ⟨o, e⟩ => e.symm ▸ omega_le_aleph _⟩

theorem aleph'_is_normal : IsNormal (ord ∘ aleph') :=
  ⟨fun o => ord_lt_ord.2 <| aleph'_lt.2 <| Ordinal.lt_succ_self _, fun o l a => by
    simp only [ord_le, aleph'_le_of_limit l]⟩

theorem aleph_is_normal : IsNormal (ord ∘ aleph) :=
  aleph'_is_normal.trans <| add_is_normal Ordinal.omega

theorem succ_omega : succ ω = aleph 1 := by
  rw [← aleph_zero, ← aleph_succ, Ordinal.succ_zero]

theorem omega_lt_aleph_one : ω < aleph 1 := by
  rw [← succ_omega]
  exact lt_succ_self _

theorem countable_iff_lt_aleph_one {α : Type _} (s : Set α) : Countable s ↔ # s < aleph 1 := by
  rw [← succ_omega, lt_succ, mk_set_le_omega]

/-- Ordinals that are cardinals are unbounded. -/
theorem ord_card_unbounded : Unbounded (· < ·) { b : Ordinal | b.card.ord = b } :=
  unbounded_lt_iff.2 fun a =>
    ⟨_,
      ⟨by
        dsimp'
        rw [card_ord], (lt_ord_succ_card a).le⟩⟩

theorem eq_aleph'_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) : ∃ a, (aleph' a).ord = o :=
  ⟨Cardinal.alephIdx.relIso o.card, by
    simpa using ho⟩

/-- `ord ∘ aleph'` enumerates the ordinals that are cardinals. -/
theorem ord_aleph'_eq_enum_card : ord ∘ aleph' = enumOrd { b : Ordinal | b.card.ord = b } := by
  rw [← eq_enum_ord _ ord_card_unbounded, range_eq_iff]
  exact
    ⟨aleph'_is_normal.strict_mono,
      ⟨fun a => by
        dsimp'
        rw [card_ord], fun b hb => eq_aleph'_of_eq_card_ord hb⟩⟩

/-- Infinite ordinals that are cardinals are unbounded. -/
theorem ord_card_unbounded' : Unbounded (· < ·) { b : Ordinal | b.card.ord = b ∧ Ordinal.omega ≤ b } :=
  (unbounded_lt_inter_le Ordinal.omega).2 ord_card_unbounded

theorem eq_aleph_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) (ho' : Ordinal.omega ≤ o) :
    ∃ a, (aleph a).ord = o := by
  cases' eq_aleph'_of_eq_card_ord ho with a ha
  use a - Ordinal.omega
  unfold aleph
  rwa [Ordinal.add_sub_cancel_of_le]
  rwa [← omega_le_aleph', ← ord_le_ord, ha, ord_omega]

/-- `ord ∘ aleph` enumerates the infinite ordinals that are cardinals. -/
theorem ord_aleph_eq_enum_card : ord ∘ aleph = enumOrd { b : Ordinal | b.card.ord = b ∧ Ordinal.omega ≤ b } := by
  rw [← eq_enum_ord _ ord_card_unbounded']
  use aleph_is_normal.strict_mono
  rw [range_eq_iff]
  refine' ⟨fun a => ⟨_, _⟩, fun b hb => eq_aleph_of_eq_card_ord hb.1 hb.2⟩
  · rw [card_ord]
    
  · rw [← ord_omega, ord_le_ord]
    exact omega_le_aleph _
    

/-! ### Properties of `mul` -/


/-- If `α` is an infinite type, then `α × α` and `α` have the same cardinality. -/
theorem mul_eq_self {c : Cardinal} (h : ω ≤ c) : c * c = c := by
  refine'
    le_antisymmₓ _
      (by
        simpa only [mul_oneₓ] using mul_le_mul_left' (one_lt_omega.le.trans h) c)
  -- the only nontrivial part is `c * c ≤ c`. We prove it inductively.
  refine' Acc.recOnₓ (cardinal.wf.apply c) (fun c _ => (Quotientₓ.induction_on c) fun α IH ol => _) h
  -- consider the minimal well-order `r` on `α` (a type with cardinality `c`).
  rcases ord_eq α with ⟨r, wo, e⟩
  skip
  let this := linearOrderOfSTO' r
  have : IsWellOrder α (· < ·) := wo
  -- Define an order `s` on `α × α` by writing `(a, b) < (c, d)` if `max a b < max c d`, or
  -- the max are equal and `a < c`, or the max are equal and `a = c` and `b < d`.
  let g : α × α → α := fun p => max p.1 p.2
  let f : α × α ↪ Ordinal × α × α := ⟨fun p : α × α => (typein (· < ·) (g p), p), fun p q => congr_argₓ Prod.snd⟩
  let s := f ⁻¹'o Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
  -- this is a well order on `α × α`.
  have : IsWellOrder _ s := (RelEmbedding.preimage _ _).IsWellOrder
  /- it suffices to show that this well order is smaller than `r`
       if it were larger, then `r` would be a strict prefix of `s`. It would be contained in
      `β × β` for some `β` of cardinality `< c`. By the inductive assumption, this set has the
      same cardinality as `β` (or it is finite if `β` is finite), so it is `< c`, which is a
      contradiction. -/
  suffices type s ≤ type r by
    exact card_le_card this
  refine' le_of_forall_lt fun o h => _
  rcases typein_surj s h with ⟨p, rfl⟩
  rw [← e, lt_ord]
  refine' lt_of_le_of_ltₓ (_ : _ ≤ card (typein (· < ·) (g p)).succ * card (typein (· < ·) (g p)).succ) _
  · have : { q | s q p } ⊆ insert (g p) { x | x < g p } ×ˢ insert (g p) { x | x < g p } := by
      intro q h
      simp only [s, embedding.coe_fn_mk, Order.Preimage, typein_lt_typein, Prod.lex_def, typein_inj] at h
      exact max_le_iff.1 (le_iff_lt_or_eqₓ.2 <| h.imp_right And.left)
    suffices H : (insert (g p) { x | r x (g p) } : Set α) ≃ Sum { x | r x (g p) } PUnit
    · exact ⟨(Set.embeddingOfSubset _ _ this).trans ((Equivₓ.Set.prod _ _).trans (H.prod_congr H)).toEmbedding⟩
      
    refine' (Equivₓ.Set.insert _).trans ((Equivₓ.refl _).sumCongr punit_equiv_punit)
    apply @irrefl _ r
    
  cases' lt_or_leₓ (card (typein (· < ·) (g p)).succ) ω with qo qo
  · exact lt_of_lt_of_leₓ (mul_lt_omega qo qo) ol
    
  · suffices
    · exact lt_of_le_of_ltₓ (IH _ this qo) this
      
    rw [← lt_ord]
    apply (ord_is_limit ol).2
    rw [mk_def, e]
    apply typein_lt_type
    

end UsingOrdinals

/-- If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem mul_eq_max {a b : Cardinal} (ha : ω ≤ a) (hb : ω ≤ b) : a * b = max a b :=
  le_antisymmₓ (mul_eq_self (le_transₓ ha (le_max_leftₓ a b)) ▸ mul_le_mul' (le_max_leftₓ _ _) (le_max_rightₓ _ _)) <|
    max_leₓ
      (by
        simpa only [mul_oneₓ] using mul_le_mul_left' (one_lt_omega.le.trans hb) a)
      (by
        simpa only [one_mulₓ] using mul_le_mul_right' (one_lt_omega.le.trans ha) b)

@[simp]
theorem mul_mk_eq_max {α β : Type _} [Infinite α] [Infinite β] : # α * # β = max (# α) (# β) :=
  mul_eq_max (omega_le_mk α) (omega_le_mk β)

@[simp]
theorem aleph_mul_aleph (o₁ o₂ : Ordinal) : aleph o₁ * aleph o₂ = aleph (max o₁ o₂) := by
  rw [Cardinal.mul_eq_max (omega_le_aleph o₁) (omega_le_aleph o₂), max_aleph_eq]

@[simp]
theorem omega_mul_eq {a : Cardinal} (ha : ω ≤ a) : ω * a = a :=
  (mul_eq_max le_rfl ha).trans (max_eq_rightₓ ha)

@[simp]
theorem mul_omega_eq {a : Cardinal} (ha : ω ≤ a) : a * ω = a :=
  (mul_eq_max ha le_rfl).trans (max_eq_leftₓ ha)

@[simp]
theorem omega_mul_mk_eq {α : Type _} [Infinite α] : ω * # α = # α :=
  omega_mul_eq (omega_le_mk α)

@[simp]
theorem mk_mul_omega_eq {α : Type _} [Infinite α] : # α * ω = # α :=
  mul_omega_eq (omega_le_mk α)

@[simp]
theorem omega_mul_aleph (o : Ordinal) : ω * aleph o = aleph o :=
  omega_mul_eq (omega_le_aleph o)

@[simp]
theorem aleph_mul_omega (o : Ordinal) : aleph o * ω = aleph o :=
  mul_omega_eq (omega_le_aleph o)

theorem mul_lt_of_lt {a b c : Cardinal} (hc : ω ≤ c) (h1 : a < c) (h2 : b < c) : a * b < c :=
  lt_of_le_of_ltₓ (mul_le_mul' (le_max_leftₓ a b) (le_max_rightₓ a b)) <|
    (lt_or_leₓ (max a b) ω).elim (fun h => lt_of_lt_of_leₓ (mul_lt_omega h h) hc) fun h => by
      rw [mul_eq_self h] <;> exact max_ltₓ h1 h2

theorem mul_le_max_of_omega_le_left {a b : Cardinal} (h : ω ≤ a) : a * b ≤ max a b := by
  convert mul_le_mul' (le_max_leftₓ a b) (le_max_rightₓ a b)
  rw [mul_eq_self]
  refine' le_transₓ h (le_max_leftₓ a b)

theorem mul_eq_max_of_omega_le_left {a b : Cardinal} (h : ω ≤ a) (h' : b ≠ 0) : a * b = max a b := by
  cases' le_or_ltₓ ω b with hb hb
  · exact mul_eq_max h hb
    
  refine' (mul_le_max_of_omega_le_left h).antisymm _
  have : b ≤ a := hb.le.trans h
  rw [max_eq_leftₓ this]
  convert mul_le_mul_left' (one_le_iff_ne_zero.mpr h') _
  rw [mul_oneₓ]

theorem mul_eq_max' {a b : Cardinal} (h : ω ≤ a * b) : a * b = max a b := by
  rcases omega_le_mul_iff.mp h with ⟨ha, hb, h⟩
  wlog h : ω ≤ a := h using a b
  exact mul_eq_max_of_omega_le_left h hb

theorem mul_le_max (a b : Cardinal) : a * b ≤ max (max a b) ω := by
  by_cases' ha0 : a = 0
  · simp [ha0]
    
  by_cases' hb0 : b = 0
  · simp [hb0]
    
  by_cases' ha : ω ≤ a
  · rw [mul_eq_max_of_omega_le_left ha hb0]
    exact le_max_leftₓ _ _
    
  · by_cases' hb : ω ≤ b
    · rw [mul_comm, mul_eq_max_of_omega_le_left hb ha0, max_commₓ]
      exact le_max_leftₓ _ _
      
    · exact le_max_of_le_right (le_of_ltₓ (mul_lt_omega (lt_of_not_geₓ ha) (lt_of_not_geₓ hb)))
      
    

theorem mul_eq_left {a b : Cardinal} (ha : ω ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) : a * b = a := by
  rw [mul_eq_max_of_omega_le_left ha hb', max_eq_leftₓ hb]

theorem mul_eq_right {a b : Cardinal} (hb : ω ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) : a * b = b := by
  rw [mul_comm, mul_eq_left hb ha ha']

theorem le_mul_left {a b : Cardinal} (h : b ≠ 0) : a ≤ b * a := by
  convert mul_le_mul_right' (one_le_iff_ne_zero.mpr h) _
  rw [one_mulₓ]

theorem le_mul_right {a b : Cardinal} (h : b ≠ 0) : a ≤ a * b := by
  rw [mul_comm]
  exact le_mul_left h

theorem mul_eq_left_iff {a b : Cardinal} : a * b = a ↔ max ω b ≤ a ∧ b ≠ 0 ∨ b = 1 ∨ a = 0 := by
  rw [max_le_iff]
  constructor
  · intro h
    cases' le_or_ltₓ ω a with ha ha
    · have : a ≠ 0 := by
        rintro rfl
        exact not_lt_of_le ha omega_pos
      left
      use ha
      · rw [← not_ltₓ]
        intro hb
        apply ne_of_gtₓ _ h
        refine' lt_of_lt_of_leₓ hb (le_mul_left this)
        
      · rintro rfl
        apply this
        rw [_root_.mul_zero] at h
        subst h
        
      
    right
    by_cases' h2a : a = 0
    · right
      exact h2a
      
    have hb : b ≠ 0 := by
      rintro rfl
      apply h2a
      rw [mul_zero] at h
      subst h
    left
    rw [← h, mul_lt_omega_iff, lt_omega, lt_omega] at ha
    rcases ha with (rfl | rfl | ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩)
    contradiction
    contradiction
    rw [← Ne] at h2a
    rw [← one_le_iff_ne_zero] at h2a hb
    norm_cast  at h2a hb h⊢
    apply le_antisymmₓ _ hb
    rw [← not_ltₓ]
    intro h2b
    apply ne_of_gtₓ _ h
    conv_lhs => rw [← mul_oneₓ n]
    rwa [mul_lt_mul_left]
    apply Nat.lt_of_succ_leₓ h2a
    
  · rintro (⟨⟨ha, hab⟩, hb⟩ | rfl | rfl)
    · rw [mul_eq_max_of_omega_le_left ha hb, max_eq_leftₓ hab]
      
    all_goals
      simp
    

/-! ### Properties of `add` -/


/-- If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality. -/
theorem add_eq_self {c : Cardinal} (h : ω ≤ c) : c + c = c :=
  le_antisymmₓ
    (by
      simpa only [Nat.cast_bit0, Nat.cast_oneₓ, mul_eq_self h, two_mul] using
        mul_le_mul_right' ((nat_lt_omega 2).le.trans h) c)
    (self_le_add_left c c)

/-- If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem add_eq_max {a b : Cardinal} (ha : ω ≤ a) : a + b = max a b :=
  le_antisymmₓ (add_eq_self (le_transₓ ha (le_max_leftₓ a b)) ▸ add_le_add (le_max_leftₓ _ _) (le_max_rightₓ _ _)) <|
    max_leₓ (self_le_add_right _ _) (self_le_add_left _ _)

theorem add_eq_max' {a b : Cardinal} (ha : ω ≤ b) : a + b = max a b := by
  rw [add_commₓ, max_commₓ, add_eq_max ha]

@[simp]
theorem add_mk_eq_max {α β : Type _} [Infinite α] : # α + # β = max (# α) (# β) :=
  add_eq_max (omega_le_mk α)

@[simp]
theorem add_mk_eq_max' {α β : Type _} [Infinite β] : # α + # β = max (# α) (# β) :=
  add_eq_max' (omega_le_mk β)

theorem add_le_max (a b : Cardinal) : a + b ≤ max (max a b) ω := by
  by_cases' ha : ω ≤ a
  · rw [add_eq_max ha]
    exact le_max_leftₓ _ _
    
  · by_cases' hb : ω ≤ b
    · rw [add_commₓ, add_eq_max hb, max_commₓ]
      exact le_max_leftₓ _ _
      
    · exact le_max_of_le_right (le_of_ltₓ (add_lt_omega (lt_of_not_geₓ ha) (lt_of_not_geₓ hb)))
      
    

theorem add_le_of_le {a b c : Cardinal} (hc : ω ≤ c) (h1 : a ≤ c) (h2 : b ≤ c) : a + b ≤ c :=
  (add_le_add h1 h2).trans <| le_of_eqₓ <| add_eq_self hc

theorem add_lt_of_lt {a b c : Cardinal} (hc : ω ≤ c) (h1 : a < c) (h2 : b < c) : a + b < c :=
  lt_of_le_of_ltₓ (add_le_add (le_max_leftₓ a b) (le_max_rightₓ a b)) <|
    (lt_or_leₓ (max a b) ω).elim (fun h => lt_of_lt_of_leₓ (add_lt_omega h h) hc) fun h => by
      rw [add_eq_self h] <;> exact max_ltₓ h1 h2

theorem eq_of_add_eq_of_omega_le {a b c : Cardinal} (h : a + b = c) (ha : a < c) (hc : ω ≤ c) : b = c := by
  apply le_antisymmₓ
  · rw [← h]
    apply self_le_add_left
    
  rw [← not_ltₓ]
  intro hb
  have : a + b < c := add_lt_of_lt hc ha hb
  simpa [h, lt_irreflₓ] using this

theorem add_eq_left {a b : Cardinal} (ha : ω ≤ a) (hb : b ≤ a) : a + b = a := by
  rw [add_eq_max ha, max_eq_leftₓ hb]

theorem add_eq_right {a b : Cardinal} (hb : ω ≤ b) (ha : a ≤ b) : a + b = b := by
  rw [add_commₓ, add_eq_left hb ha]

theorem add_eq_left_iff {a b : Cardinal} : a + b = a ↔ max ω b ≤ a ∨ b = 0 := by
  rw [max_le_iff]
  constructor
  · intro h
    cases' le_or_ltₓ ω a with ha ha
    · left
      use ha
      rw [← not_ltₓ]
      intro hb
      apply ne_of_gtₓ _ h
      exact lt_of_lt_of_leₓ hb (self_le_add_left b a)
      
    right
    rw [← h, add_lt_omega_iff, lt_omega, lt_omega] at ha
    rcases ha with ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩
    norm_cast  at h⊢
    rw [← add_right_injₓ, h, add_zeroₓ]
    
  · rintro (⟨h1, h2⟩ | h3)
    rw [add_eq_max h1, max_eq_leftₓ h2]
    rw [h3, add_zeroₓ]
    

theorem add_eq_right_iff {a b : Cardinal} : a + b = b ↔ max ω a ≤ b ∨ a = 0 := by
  rw [add_commₓ, add_eq_left_iff]

theorem add_one_eq {a : Cardinal} (ha : ω ≤ a) : a + 1 = a :=
  have : 1 ≤ a := le_transₓ (le_of_ltₓ one_lt_omega) ha
  add_eq_left ha this

@[simp]
theorem mk_add_one_eq {α : Type _} [Infinite α] : # α + 1 = # α :=
  add_one_eq (omega_le_mk α)

protected theorem eq_of_add_eq_add_left {a b c : Cardinal} (h : a + b = a + c) (ha : a < ω) : b = c := by
  cases' le_or_ltₓ ω b with hb hb
  · have : a < b := lt_of_lt_of_leₓ ha hb
    rw [add_eq_right hb (le_of_ltₓ this), eq_comm] at h
    rw [eq_of_add_eq_of_omega_le h this hb]
    
  · have hc : c < ω := by
      rw [← not_leₓ]
      intro hc
      apply lt_irreflₓ ω
      apply lt_of_le_of_ltₓ (le_transₓ hc (self_le_add_left _ a))
      rw [← h]
      apply add_lt_omega ha hb
    rw [lt_omega] at *
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    rcases hc with ⟨k, rfl⟩
    norm_cast  at h⊢
    apply add_left_cancelₓ h
    

protected theorem eq_of_add_eq_add_right {a b c : Cardinal} (h : a + b = c + b) (hb : b < ω) : a = c := by
  rw [add_commₓ a b, add_commₓ c b] at h
  exact Cardinal.eq_of_add_eq_add_left h hb

@[simp]
theorem aleph_add_aleph (o₁ o₂ : Ordinal) : aleph o₁ + aleph o₂ = aleph (max o₁ o₂) := by
  rw [Cardinal.add_eq_max (omega_le_aleph o₁), max_aleph_eq]

theorem principal_add_ord {c : Cardinal} (hc : ω ≤ c) : Ordinal.Principal (· + ·) c.ord := fun a b ha hb => by
  rw [lt_ord, Ordinal.card_add] at *
  exact add_lt_of_lt hc ha hb

theorem principal_add_aleph (o : Ordinal) : Ordinal.Principal (· + ·) (aleph o).ord :=
  principal_add_ord <| omega_le_aleph o

/-! ### Properties about power -/


theorem pow_le {κ μ : Cardinal.{u}} (H1 : ω ≤ κ) (H2 : μ < ω) : κ ^ μ ≤ κ :=
  let ⟨n, H3⟩ := lt_omega.1 H2
  H3.symm ▸
    Quotientₓ.induction_on κ
      (fun α H1 =>
        Nat.recOn n
          (le_of_ltₓ <|
            lt_of_lt_of_leₓ
              (by
                rw [Nat.cast_zeroₓ, power_zero] <;> exact one_lt_omega)
              H1)
          fun n ih =>
          trans_rel_left _
            (by
              rw [Nat.cast_succₓ, power_add, power_one] <;> exact mul_le_mul_right' ih _)
            (mul_eq_self H1))
      H1

theorem pow_eq {κ μ : Cardinal.{u}} (H1 : ω ≤ κ) (H2 : 1 ≤ μ) (H3 : μ < ω) : κ ^ μ = κ :=
  (pow_le H1 H3).antisymm <| self_le_power κ H2

theorem power_self_eq {c : Cardinal} (h : ω ≤ c) : c ^ c = 2 ^ c := by
  apply le_antisymmₓ
  · apply le_transₓ (power_le_power_right <| le_of_ltₓ <| cantor c)
    rw [← power_mul, mul_eq_self h]
    
  · convert power_le_power_right (le_transₓ (le_of_ltₓ <| nat_lt_omega 2) h)
    apply nat.cast_two.symm
    

theorem prod_eq_two_power {ι : Type u} [Infinite ι] {c : ι → Cardinal.{v}} (h₁ : ∀ i, 2 ≤ c i)
    (h₂ : ∀ i, lift.{u} (c i) ≤ lift.{v} (# ι)) : prod c = 2 ^ lift.{v} (# ι) := by
  rw [← lift_id' (Prod c), lift_prod, ← lift_two_power]
  apply le_antisymmₓ
  · refine' (prod_le_prod _ _ h₂).trans_eq _
    rw [prod_const, lift_lift, ← lift_power, power_self_eq (omega_le_mk ι), lift_umax.{u, v}]
    
  · rw [← prod_const', lift_prod]
    refine' prod_le_prod _ _ fun i => _
    rw [lift_two, ← lift_two.{u, v}, lift_le]
    exact h₁ i
    

theorem power_eq_two_power {c₁ c₂ : Cardinal} (h₁ : ω ≤ c₁) (h₂ : 2 ≤ c₂) (h₂' : c₂ ≤ c₁) : c₂ ^ c₁ = 2 ^ c₁ :=
  le_antisymmₓ (power_self_eq h₁ ▸ power_le_power_right h₂') (power_le_power_right h₂)

theorem nat_power_eq {c : Cardinal.{u}} (h : ω ≤ c) {n : ℕ} (hn : 2 ≤ n) : (n : Cardinal.{u}) ^ c = 2 ^ c :=
  power_eq_two_power h
    (by
      assumption_mod_cast)
    ((nat_lt_omega n).le.trans h)

theorem power_nat_le {c : Cardinal.{u}} {n : ℕ} (h : ω ≤ c) : c ^ n ≤ c :=
  pow_le h (nat_lt_omega n)

theorem power_nat_eq {c : Cardinal.{u}} {n : ℕ} (h1 : ω ≤ c) (h2 : 1 ≤ n) : c ^ n = c :=
  pow_eq h1
    (by
      exact_mod_cast h2)
    (nat_lt_omega n)

theorem power_nat_le_max {c : Cardinal.{u}} {n : ℕ} : c ^ (n : Cardinal.{u}) ≤ max c ω := by
  by_cases' hc : ω ≤ c
  · exact le_max_of_le_left (power_nat_le hc)
    
  · exact le_max_of_le_right (le_of_ltₓ (power_lt_omega (lt_of_not_geₓ hc) (nat_lt_omega _)))
    

@[simp]
theorem powerlt_omega {c : Cardinal} (h : ω ≤ c) : c ^< ω = c := by
  apply le_antisymmₓ
  · rw [powerlt_le]
    intro c'
    rw [lt_omega]
    rintro ⟨n, rfl⟩
    apply power_nat_le h
    
  convert le_powerlt one_lt_omega
  rw [power_one]

theorem powerlt_omega_le (c : Cardinal) : c ^< ω ≤ max c ω := by
  cases le_or_ltₓ ω c
  · rw [powerlt_omega h]
    apply le_max_leftₓ
    
  rw [powerlt_le]
  intro c' hc'
  refine' le_transₓ (le_of_ltₓ <| power_lt_omega h hc') (le_max_rightₓ _ _)

/-! ### Computing cardinality of various types -/


theorem mk_list_eq_mk (α : Type u) [Infinite α] : # (List α) = # α :=
  have H1 : ω ≤ # α := omega_le_mk α
  Eq.symm <|
    le_antisymmₓ ⟨⟨fun x => [x], fun x y H => (List.cons.injₓ H).1⟩⟩ <|
      calc
        # (List α) = sum fun n : ℕ => # α ^ (n : Cardinal.{u}) := mk_list_eq_sum_pow α
        _ ≤ sum fun n : ℕ => # α := (sum_le_sum _ _) fun n => pow_le H1 <| nat_lt_omega n
        _ = # α := by
          simp [H1]
        

theorem mk_list_eq_omega (α : Type u) [Encodable α] [Nonempty α] : # (List α) = ω :=
  mk_le_omega.antisymm (omega_le_mk _)

theorem mk_list_eq_max_mk_omega (α : Type u) [Nonempty α] : # (List α) = max (# α) ω := by
  cases fintypeOrInfinite α
  · have : Encodable α := Fintype.toEncodable α
    rw [mk_list_eq_omega, eq_comm, max_eq_rightₓ]
    exact mk_le_omega
    
  · rw [mk_list_eq_mk, eq_comm, max_eq_leftₓ]
    exact omega_le_mk α
    

theorem mk_list_le_max (α : Type u) : # (List α) ≤ max ω (# α) := by
  cases fintypeOrInfinite α
  · have := Fintype.toEncodable α
    exact mk_le_omega.trans (le_max_leftₓ _ _)
    
  · rw [mk_list_eq_mk]
    apply le_max_rightₓ
    

theorem mk_finset_eq_mk (α : Type u) [Infinite α] : # (Finset α) = # α :=
  Eq.symm <|
    le_antisymmₓ (mk_le_of_injective fun x y => Finset.singleton_inj.1) <|
      calc
        # (Finset α) ≤ # (List α) := mk_le_of_surjective List.to_finset_surjective
        _ = # α := mk_list_eq_mk α
        

theorem mk_bounded_set_le_of_infinite (α : Type u) [Infinite α] (c : Cardinal) :
    # { t : Set α // mk t ≤ c } ≤ # α ^ c := by
  refine'
    le_transₓ _
      (by
        rw [← add_one_eq (omega_le_mk α)])
  induction' c using Cardinal.induction_on with β
  fapply mk_le_of_surjective
  · intro f
    use Sum.inl ⁻¹' range f
    refine' le_transₓ (mk_preimage_of_injective _ _ fun x y => Sum.inl.injₓ) _
    apply mk_range_le
    
  rintro ⟨s, ⟨g⟩⟩
  use fun y => if h : ∃ x : s, g x = y then Sum.inl (Classical.some h).val else Sum.inr ⟨⟩
  apply Subtype.eq
  ext
  constructor
  · rintro ⟨y, h⟩
    dsimp' only  at h
    by_cases' h' : ∃ z : s, g z = y
    · rw [dif_pos h'] at h
      cases Sum.inl.injₓ h
      exact (Classical.some h').2
      
    · rw [dif_neg h'] at h
      cases h
      
    
  · intro h
    have : ∃ z : s, g z = g ⟨x, h⟩ := ⟨⟨x, h⟩, rfl⟩
    use g ⟨x, h⟩
    dsimp' only
    rw [dif_pos this]
    congr
    suffices : Classical.some this = ⟨x, h⟩
    exact congr_argₓ Subtype.val this
    apply g.2
    exact Classical.some_spec this
    

theorem mk_bounded_set_le (α : Type u) (c : Cardinal) : # { t : Set α // # t ≤ c } ≤ max (# α) ω ^ c := by
  trans # { t : Set (Sum (ULift.{u} ℕ) α) // # t ≤ c }
  · refine' ⟨embedding.subtype_map _ _⟩
    apply embedding.image
    use Sum.inr
    apply Sum.inr.injₓ
    intro s hs
    exact le_transₓ mk_image_le hs
    
  refine' le_transₓ (mk_bounded_set_le_of_infinite (Sum (ULift.{u} ℕ) α) c) _
  rw [max_commₓ, ← add_eq_max] <;> rfl

theorem mk_bounded_subset_le {α : Type u} (s : Set α) (c : Cardinal.{u}) :
    # { t : Set α // t ⊆ s ∧ # t ≤ c } ≤ max (# s) ω ^ c := by
  refine' le_transₓ _ (mk_bounded_set_le s c)
  refine' ⟨embedding.cod_restrict _ _ _⟩
  use fun t => coe ⁻¹' t.1
  · rintro ⟨t, ht1, ht2⟩ ⟨t', h1t', h2t'⟩ h
    apply Subtype.eq
    dsimp' only  at h⊢
    refine' (preimage_eq_preimage' _ _).1 h <;> rw [Subtype.range_coe] <;> assumption
    
  rintro ⟨t, h1t, h2t⟩
  exact le_transₓ (mk_preimage_of_injective _ _ Subtype.val_injective) h2t

/-! ### Properties of `compl` -/


theorem mk_compl_of_infinite {α : Type _} [Infinite α] (s : Set α) (h2 : # s < # α) : # (sᶜ : Set α) = # α := by
  refine' eq_of_add_eq_of_omega_le _ h2 (omega_le_mk α)
  exact mk_sum_compl s

theorem mk_compl_finset_of_infinite {α : Type _} [Infinite α] (s : Finset α) : # (↑sᶜ : Set α) = # α := by
  apply mk_compl_of_infinite
  exact (finset_card_lt_omega s).trans_le (omega_le_mk α)

theorem mk_compl_eq_mk_compl_infinite {α : Type _} [Infinite α] {s t : Set α} (hs : # s < # α) (ht : # t < # α) :
    # (sᶜ : Set α) = # (tᶜ : Set α) := by
  rw [mk_compl_of_infinite s hs, mk_compl_of_infinite t ht]

theorem mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} [Fintype α] {s : Set α} {t : Set β}
    (h1 : lift.{max v w} (# α) = lift.{max u w} (# β)) (h2 : lift.{max v w} (# s) = lift.{max u w} (# t)) :
    lift.{max v w} (# (sᶜ : Set α)) = lift.{max u w} (# (tᶜ : Set β)) := by
  rcases lift_mk_eq.1 h1 with ⟨e⟩
  let this : Fintype β := Fintype.ofEquiv α e
  replace h1 : Fintype.card α = Fintype.card β := (Fintype.of_equiv_card _).symm
  classical
  lift s to Finset α using finite.of_fintype s
  lift t to Finset β using finite.of_fintype t
  simp only [Finset.coe_sort_coe, mk_finset, lift_nat_cast, Nat.cast_inj] at h2
  simp only [← Finset.coe_compl, Finset.coe_sort_coe, mk_finset, Finset.card_compl, lift_nat_cast, Nat.cast_inj, h1, h2]

theorem mk_compl_eq_mk_compl_finite {α β : Type u} [Fintype α] {s : Set α} {t : Set β} (h1 : # α = # β)
    (h : # s = # t) : # (sᶜ : Set α) = # (tᶜ : Set β) := by
  rw [← lift_inj]
  apply mk_compl_eq_mk_compl_finite_lift <;> rwa [lift_inj]

theorem mk_compl_eq_mk_compl_finite_same {α : Type _} [Fintype α] {s t : Set α} (h : # s = # t) :
    # (sᶜ : Set α) = # (tᶜ : Set α) :=
  mk_compl_eq_mk_compl_finite rfl h

/-! ### Extending an injection to an equiv -/


theorem extend_function {α β : Type _} {s : Set α} (f : s ↪ β) (h : Nonempty ((sᶜ : Set α) ≃ (Range fᶜ : Set β))) :
    ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  intros
  have := h
  cases' this with g
  let h : α ≃ β :=
    (set.sum_compl (s : Set α)).symm.trans ((sum_congr (Equivₓ.ofInjective f f.2) g).trans (set.sum_compl (range f)))
  refine' ⟨h, _⟩
  rintro ⟨x, hx⟩
  simp [set.sum_compl_symm_apply_of_mem, hx]

theorem extend_function_finite {α β : Type _} [Fintype α] {s : Set α} (f : s ↪ β) (h : Nonempty (α ≃ β)) :
    ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  apply extend_function f
  cases' id h with g
  rw [← lift_mk_eq] at h
  rw [← lift_mk_eq, mk_compl_eq_mk_compl_finite_lift h]
  rw [mk_range_eq_lift]
  exact f.2

theorem extend_function_of_lt {α β : Type _} {s : Set α} (f : s ↪ β) (hs : # s < # α) (h : Nonempty (α ≃ β)) :
    ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  cases fintypeOrInfinite α
  · exact extend_function_finite f h
    
  · apply extend_function f
    cases' id h with g
    have := Infinite.of_injective _ g.injective
    rw [← lift_mk_eq'] at h⊢
    rwa [mk_compl_of_infinite s hs, mk_compl_of_infinite]
    rwa [← lift_lt, mk_range_eq_of_injective f.injective, ← h, lift_lt]
    

section Bit

/-!
This section proves inequalities for `bit0` and `bit1`, enabling `simp` to solve inequalities
for numeral cardinals. The complexity of the resulting algorithm is not good, as in some cases
`simp` reduces an inequality to a disjunction of two situations, depending on whether a cardinal
is finite or infinite. Since the evaluation of the branches is not lazy, this is bad. It is good
enough for practical situations, though.

For specific numbers, these inequalities could also be deduced from the corresponding
inequalities of natural numbers using `norm_cast`:
```
example : (37 : cardinal) < 42 :=
by { norm_cast, norm_num }
```
-/


theorem bit0_ne_zero (a : Cardinal) : ¬bit0 a = 0 ↔ ¬a = 0 := by
  simp [bit0]

@[simp]
theorem bit1_ne_zero (a : Cardinal) : ¬bit1 a = 0 := by
  simp [bit1]

@[simp]
theorem zero_lt_bit0 (a : Cardinal) : 0 < bit0 a ↔ 0 < a := by
  rw [← not_iff_not]
  simp [bit0]

@[simp]
theorem zero_lt_bit1 (a : Cardinal) : 0 < bit1 a :=
  lt_of_lt_of_leₓ zero_lt_one (self_le_add_left _ _)

@[simp]
theorem one_le_bit0 (a : Cardinal) : 1 ≤ bit0 a ↔ 0 < a :=
  ⟨fun h => (zero_lt_bit0 a).mp (lt_of_lt_of_leₓ zero_lt_one h), fun h =>
    le_transₓ (one_le_iff_pos.mpr h) (self_le_add_left a a)⟩

@[simp]
theorem one_le_bit1 (a : Cardinal) : 1 ≤ bit1 a :=
  self_le_add_left _ _

theorem bit0_eq_self {c : Cardinal} (h : ω ≤ c) : bit0 c = c :=
  add_eq_self h

@[simp]
theorem bit0_lt_omega {c : Cardinal} : bit0 c < ω ↔ c < ω := by
  simp [bit0, add_lt_omega_iff]

@[simp]
theorem omega_le_bit0 {c : Cardinal} : ω ≤ bit0 c ↔ ω ≤ c := by
  rw [← not_iff_not]
  simp

@[simp]
theorem bit1_eq_self_iff {c : Cardinal} : bit1 c = c ↔ ω ≤ c := by
  by_cases' h : ω ≤ c
  · simp only [bit1, bit0_eq_self h, h, eq_self_iff_true, add_one_of_omega_le]
    
  · refine' iff_of_false (ne_of_gtₓ _) h
    rcases lt_omega.1 (not_leₓ.1 h) with ⟨n, rfl⟩
    norm_cast
    dsimp' [bit1, bit0]
    linarith
    

@[simp]
theorem bit1_lt_omega {c : Cardinal} : bit1 c < ω ↔ c < ω := by
  simp [bit1, bit0, add_lt_omega_iff, one_lt_omega]

@[simp]
theorem omega_le_bit1 {c : Cardinal} : ω ≤ bit1 c ↔ ω ≤ c := by
  rw [← not_iff_not]
  simp

@[simp]
theorem bit0_le_bit0 {a b : Cardinal} : bit0 a ≤ bit0 b ↔ a ≤ b := by
  cases' le_or_ltₓ ω a with ha ha <;> cases' le_or_ltₓ ω b with hb hb
  · rw [bit0_eq_self ha, bit0_eq_self hb]
    
  · rw [bit0_eq_self ha]
    refine' iff_of_false (fun h => _) (not_le_of_lt (hb.trans_le ha))
    have A : bit0 b < ω := by
      simpa using hb
    exact lt_irreflₓ _ (lt_of_lt_of_leₓ (lt_of_lt_of_leₓ A ha) h)
    
  · rw [bit0_eq_self hb]
    exact iff_of_true ((bit0_lt_omega.2 ha).le.trans hb) (ha.le.trans hb)
    
  · rcases lt_omega.1 ha with ⟨m, rfl⟩
    rcases lt_omega.1 hb with ⟨n, rfl⟩
    norm_cast
    exact bit0_le_bit0
    

@[simp]
theorem bit0_le_bit1 {a b : Cardinal} : bit0 a ≤ bit1 b ↔ a ≤ b := by
  cases' le_or_ltₓ ω a with ha ha <;> cases' le_or_ltₓ ω b with hb hb
  · rw [bit0_eq_self ha, bit1_eq_self_iff.2 hb]
    
  · rw [bit0_eq_self ha]
    refine' iff_of_false (fun h => _) (not_le_of_lt (hb.trans_le ha))
    have A : bit1 b < ω := by
      simpa using hb
    exact lt_irreflₓ _ (lt_of_lt_of_leₓ (lt_of_lt_of_leₓ A ha) h)
    
  · rw [bit1_eq_self_iff.2 hb]
    exact iff_of_true ((bit0_lt_omega.2 ha).le.trans hb) (ha.le.trans hb)
    
  · rcases lt_omega.1 ha with ⟨m, rfl⟩
    rcases lt_omega.1 hb with ⟨n, rfl⟩
    norm_cast
    exact Nat.bit0_le_bit1_iff
    

@[simp]
theorem bit1_le_bit1 {a b : Cardinal} : bit1 a ≤ bit1 b ↔ a ≤ b := by
  constructor
  · intro h
    apply bit0_le_bit1.1 (le_transₓ (self_le_add_right (bit0 a) 1) h)
    
  · intro h
    calc a + a + 1 ≤ a + b + 1 := add_le_add_right (add_le_add_left h a) 1_ ≤ b + b + 1 :=
        add_le_add_right (add_le_add_right h b) 1
    

@[simp]
theorem bit1_le_bit0 {a b : Cardinal} : bit1 a ≤ bit0 b ↔ a < b ∨ a ≤ b ∧ ω ≤ a := by
  cases' le_or_ltₓ ω a with ha ha <;> cases' le_or_ltₓ ω b with hb hb
  · simp only [bit1_eq_self_iff.mpr ha, bit0_eq_self hb, ha, and_trueₓ]
    refine' ⟨fun h => Or.inr h, fun h => _⟩
    cases h
    · exact le_of_ltₓ h
      
    · exact h
      
    
  · rw [bit1_eq_self_iff.2 ha]
    refine' iff_of_false (fun h => _) fun h => _
    · have A : bit0 b < ω := by
        simpa using hb
      exact lt_irreflₓ _ (lt_of_lt_of_leₓ (lt_of_lt_of_leₓ A ha) h)
      
    · exact not_le_of_lt (hb.trans_le ha) (h.elim le_of_ltₓ And.left)
      
    
  · rw [bit0_eq_self hb]
    exact iff_of_true ((bit1_lt_omega.2 ha).le.trans hb) (Or.inl <| ha.trans_le hb)
    
  · rcases lt_omega.1 ha with ⟨m, rfl⟩
    rcases lt_omega.1 hb with ⟨n, rfl⟩
    norm_cast
    simp [not_le.mpr ha]
    

@[simp]
theorem bit0_lt_bit0 {a b : Cardinal} : bit0 a < bit0 b ↔ a < b := by
  cases' le_or_ltₓ ω a with ha ha <;> cases' le_or_ltₓ ω b with hb hb
  · rw [bit0_eq_self ha, bit0_eq_self hb]
    
  · rw [bit0_eq_self ha]
    refine' iff_of_false (fun h => _) (not_lt_of_le (hb.le.trans ha))
    have A : bit0 b < ω := by
      simpa using hb
    exact lt_irreflₓ _ (lt_transₓ (lt_of_lt_of_leₓ A ha) h)
    
  · rw [bit0_eq_self hb]
    exact iff_of_true ((bit0_lt_omega.2 ha).trans_le hb) (ha.trans_le hb)
    
  · rcases lt_omega.1 ha with ⟨m, rfl⟩
    rcases lt_omega.1 hb with ⟨n, rfl⟩
    norm_cast
    exact bit0_lt_bit0
    

@[simp]
theorem bit1_lt_bit0 {a b : Cardinal} : bit1 a < bit0 b ↔ a < b := by
  cases' le_or_ltₓ ω a with ha ha <;> cases' le_or_ltₓ ω b with hb hb
  · rw [bit1_eq_self_iff.2 ha, bit0_eq_self hb]
    
  · rw [bit1_eq_self_iff.2 ha]
    refine' iff_of_false (fun h => _) (not_lt_of_le (hb.le.trans ha))
    have A : bit0 b < ω := by
      simpa using hb
    exact lt_irreflₓ _ (lt_transₓ (lt_of_lt_of_leₓ A ha) h)
    
  · rw [bit0_eq_self hb]
    exact iff_of_true ((bit1_lt_omega.2 ha).trans_le hb) (ha.trans_le hb)
    
  · rcases lt_omega.1 ha with ⟨m, rfl⟩
    rcases lt_omega.1 hb with ⟨n, rfl⟩
    norm_cast
    exact Nat.bit1_lt_bit0_iff
    

@[simp]
theorem bit1_lt_bit1 {a b : Cardinal} : bit1 a < bit1 b ↔ a < b := by
  cases' le_or_ltₓ ω a with ha ha <;> cases' le_or_ltₓ ω b with hb hb
  · rw [bit1_eq_self_iff.2 ha, bit1_eq_self_iff.2 hb]
    
  · rw [bit1_eq_self_iff.2 ha]
    refine' iff_of_false (fun h => _) (not_lt_of_le (hb.le.trans ha))
    have A : bit1 b < ω := by
      simpa using hb
    exact lt_irreflₓ _ (lt_transₓ (lt_of_lt_of_leₓ A ha) h)
    
  · rw [bit1_eq_self_iff.2 hb]
    exact iff_of_true ((bit1_lt_omega.2 ha).trans_le hb) (ha.trans_le hb)
    
  · rcases lt_omega.1 ha with ⟨m, rfl⟩
    rcases lt_omega.1 hb with ⟨n, rfl⟩
    norm_cast
    exact bit1_lt_bit1
    

@[simp]
theorem bit0_lt_bit1 {a b : Cardinal} : bit0 a < bit1 b ↔ a < b ∨ a ≤ b ∧ a < ω := by
  cases' le_or_ltₓ ω a with ha ha <;> cases' le_or_ltₓ ω b with hb hb
  · simp [bit0_eq_self ha, bit1_eq_self_iff.2 hb, not_lt.mpr ha]
    
  · rw [bit0_eq_self ha]
    refine' iff_of_false (fun h => _) fun h => _
    · have A : bit1 b < ω := by
        simpa using hb
      exact lt_irreflₓ _ (lt_transₓ (lt_of_lt_of_leₓ A ha) h)
      
    · exact not_le_of_lt (hb.trans_le ha) (h.elim le_of_ltₓ And.left)
      
    
  · rw [bit1_eq_self_iff.2 hb]
    exact iff_of_true ((bit0_lt_omega.2 ha).trans_le hb) (Or.inl <| ha.trans_le hb)
    
  · rcases lt_omega.1 ha with ⟨m, rfl⟩
    rcases lt_omega.1 hb with ⟨n, rfl⟩
    norm_cast
    simp only [ha, and_trueₓ, Nat.bit0_lt_bit1_iff, or_iff_right_of_imp le_of_ltₓ]
    

theorem one_lt_two : (1 : Cardinal) < 2 := by
  -- This strategy works generally to prove inequalities between numerals in `cardinality`.
  norm_cast
  norm_num

@[simp]
theorem one_lt_bit0 {a : Cardinal} : 1 < bit0 a ↔ 0 < a := by
  simp [← bit1_zero]

@[simp]
theorem one_lt_bit1 (a : Cardinal) : 1 < bit1 a ↔ 0 < a := by
  simp [← bit1_zero]

@[simp]
theorem one_le_one : (1 : Cardinal) ≤ 1 :=
  le_rfl

end Bit

end Cardinal

