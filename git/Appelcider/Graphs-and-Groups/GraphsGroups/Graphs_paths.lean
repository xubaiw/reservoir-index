structure Graph(V: Type) (E: Type) where
  null : E
  init : E → V
  bar : E → E
  barInv : bar ∘ bar = id
  barNoFP : ∀ e: E, bar e ≠ e
  
variable {V: Type}{E: Type}[DecidableEq V][DecidableEq E]{x1 x2 : V} 


@[inline] def term (graph: Graph V E): E → V :=
  fun e => graph.init (graph.bar e)

inductive EdgePath (graph: Graph V E): V → V → Type where
  | single : (x: V) → EdgePath graph x x 
  | cons : {x y z : V} → (e : E) → graph.init e = x → term graph e = y →  
        EdgePath graph y z → EdgePath graph x z

def EdgePath.length {graph: Graph V E}{x y: V}: EdgePath graph x y → Nat
  | EdgePath.single x => 0
  | EdgePath.cons  _ _ _ path => length path + 1 


open EdgePath

-- concatenates two edgepaths 
def multiply {G : Graph V E} {x y z : V}: (EdgePath G x y) → (EdgePath G y z) → (EdgePath G x z) := by 
intro p q
match p with
| single x => exact q
| cons ex h1 h2 exy => exact (cons ex h1 h2 (multiply exy q))



--proves that the endpoint of the reverse of an edge is the start point of the edge
theorem lemma1 {G : Graph V E} {x : V}{e : E}: G.init e = x → (term G (G.bar e) = x) :=
by
intro h
have h1 : G.bar (G.bar e) = e := congr G.barInv (Eq.refl e) 
have h2 : G.init (G.bar (G.bar e)) = G.init e := congrArg G.init h1 
apply Eq.trans h2 h

--proves that initial vertex of reversed edge is the terminal vertex of the original edge
theorem lemma1' {G : Graph V E} {x :V} {e : E}: (term G e = x) → G.init (G.bar e) = x:= by
intro hyp
have : G.init (G.bar e) = term G e := by rfl
exact Eq.trans this hyp 

-- proves associativity of path multiplication
theorem mult_assoc {G : Graph V E} (p : EdgePath G w x) (q : EdgePath G x y) (r : EdgePath G y z):
      (multiply (multiply p q) r) = (multiply p (multiply q r)) := by
      induction p with
      | single w => simp[multiply]
      | cons ex h1 h2 exy ih => simp[multiply, ih]

--proves that "single x" is an identity element for multiplication
theorem mult_const {G : Graph V E} {p : EdgePath G x y} : 
      (multiply p (single y)) = p := by
      induction p with
      | single x => simp [multiply] 
      | cons ex h1 h2 exy ih => simp[multiply, ih] 

-- reverses an edgepath
def inverse {G : Graph V E} {x y : V}: (EdgePath G x y) → (EdgePath G y x)
| single x => single x 
| cons ex h1 h2 exy => multiply (inverse exy) (cons (G.bar (ex)) h2 (lemma1 h1) (single x)) 

example {G : Graph V E } { x y z : V} (ih : x = y) (p : EdgePath G x z) : length p = length (ih ▸ p) := by 
induction ih with
| refl => rfl

def reducePath0 {G : Graph V E} {x y z : V} (ex : E) (h1 : G.init ex = x) (h2 : term G ex = y) (exy : EdgePath G y z) : { rp : EdgePath G x z // rp.length ≤ (cons ex h1 h2 exy).length} := by
cases exy with
 | single x => exact ⟨cons ex h1 h2 (single y), by simp⟩ 
 | cons ey h3 h4 eyz => 
   apply
  if c : (x = term G ey) ∧ (ey = G.bar (ex)) then
  ⟨ Eq.symm (Eq.trans (And.left c) h4) ▸ eyz, by 
      have h5 : (Eq.symm (Eq.trans (And.left c) h4) ▸ eyz).length = eyz.length := by 
        let ih := Eq.symm (Eq.trans (And.left c) h4)
        cases ih with
        | refl => rfl
      simp[EdgePath.length, h5, Nat.le_trans (Nat.le_succ (length eyz)) (Nat.le_succ (length eyz +1))]
  ⟩ 
  else
  ⟨ cons ex h1 h2 (cons ey h3 h4 (eyz)), by apply Nat.le_refl⟩ 


-- reduces given path such that no two consecutive edges are inverses of each other
def reducePath {G : Graph V E} : (p : EdgePath G x y ) → 
  {rp : EdgePath G x y // rp.length ≤ p.length} 
| single x => ⟨single x, by simp⟩
| cons ex h1 h2 ey'y => 
 -- have h5': length ey'y < length (cons ex h1 h2 ey'y) := by simp[EdgePath.length, Nat.lt_succ_self]
  let ⟨ey'z, ih1⟩ := reducePath ey'y 
  let ⟨ ez, ih⟩ := reducePath0 ex h1 h2 ey'z 
  ⟨ ez , by 
          have : length (cons ex h1 h2 ey'z) = length ey'z + 1 := by simp[length]
          let k := this ▸ ih
          have pr : length ey'z +1 ≤ length ey'y +1 := by apply Nat.succ_le_succ ih1
          simp[length, Nat.le_trans k pr] ⟩ 

termination_by _ _ _ _ p => p.length
decreasing_by 
simp_wf
simp[EdgePath.length, Nat.lt_succ_self]


--defines moves allowing homotopy of edgepaths
inductive basicht {G : Graph V E} : EdgePath G x y → EdgePath G x y → Sort where
| consht : (x : V) → (basicht (single x) (single x)) -- constant homotopy
| cancel : (ex ex' : E) → { x w y : V} → (p : EdgePath G x y) → -- cancelling consecutive opposite edges from a path
           (h : G.init ex = x) → (h1 : term G ex = w) → (t : G.bar ex = ex') → 
           basicht p (cons ex h h1 (cons ex' (t ▸ lemma1' h1) (t ▸ lemma1 h) p))
| mult : {x y z : V} → {p q : EdgePath G y z} →   -- adding an edge to homotopic paths
         basicht p q → (ex : E) →(h1 : G.init ex = x) → ( h : term G ex = y)→ 
         basicht (cons ex h1 h p) (cons ex h1 h q)

--defines the set of homotopy classes of edgepaths from x to y
def ht (G : Graph V E) (x y : V) := Quot (@basicht V E G x y )

def htclass {G : Graph V E} {x y : V} ( p : EdgePath G x y) : ht G x y :=
  Quot.mk (@basicht V E G x y ) p  
 
def homotopy {G : Graph V E} {x y : V} ( p' q' : EdgePath G x y) : Prop := 
  htclass p' = htclass q'

--proves that homotopy is a transitive relation
theorem homotopy_trans {G : Graph V E} {x y : V} (p q r : EdgePath G x y) : homotopy p q → homotopy q r → homotopy p r := by
intro h₁ h₂ 
simp[homotopy, htclass]
have p₁ : Quot.mk basicht p = Quot.mk basicht q := by apply h₁
have p₂ : Quot.mk basicht q = Quot.mk basicht r := by apply h₂
apply Eq.trans p₁ p₂ 

--proves that homotopy is preserved by multiplying an edge
theorem homotopy_left_mult_edge {G : Graph V E} {x y z : V}: (p q : EdgePath G y z) → homotopy p q → (ex : E) →(h1 : G.init ex = x) → ( h : term G ex = y)→ homotopy (cons ex h1 h p) (cons ex h1 h q) := by
  intro p q h ex h1 h2 
  let func (r : EdgePath G y z) : ht G x z := htclass (cons ex h1 h2 r)
  have g : (r₁ r₂ : EdgePath G y z) →  basicht r₁ r₂ → func r₁ = func r₂ := by
     intro r₁ r₂ h₁ 
     let t := basicht.mult h₁ ex h1 h2
     have : htclass (cons ex h1 h2 r₁) = htclass (cons ex h1 h2 r₂) := by simp[htclass]; apply Quot.sound t
     simp[this]
  simp[homotopy]
  let k := Quot.lift func g
  apply congrArg k h


--proves that homotopy is left multiplicative
theorem homotopy_left_mult {G : Graph V E} {x y z : V} (p1 p2 : EdgePath G y z) (q : EdgePath G x y) (h :homotopy p1 p2):
         (homotopy (multiply q p1) (multiply q p2)) := by
         induction q with
        | single w  => 
          simp [multiply, h]
        | cons ex h1 h2 exy ih =>
          let c := ih p1 p2 h
          have t₁ : multiply (cons ex h1 h2 exy) p1 = cons ex h1 h2 (multiply exy p1) := by simp[multiply, mult_assoc]
          have t₂ : multiply (cons ex h1 h2 exy) p2 = cons ex h1 h2 (multiply exy p2) := by simp[multiply, mult_assoc]
          rw[t₁, t₂]
          simp[homotopy_left_mult_edge, c]






/-theorem homotopy_reverse {G : Graph V E} {x y : V} (p1 p2 : EdgePath G x y) : homotopy p1 p2 → homotopy (inverse p1) (inverse p2) := by
        intro h
        induction p1 with
        | single x => 
              induction h with
              | consht z => simp[inverse]
              | cancel ex p h h1 =>
              | mult h' h1 h2 => 
        |  cons ex h1 h2 exy =>-/

/-theorem homotopy_right_mult {V : Type} {E : Type} {G : Graph V E} {x y z : V} (p1 p2 : EdgePath G x y) (q : EdgePath G y z) (h :homotopy p1 p2):
        (homotopy (multiply p1 q) (multiply p2 q)) := by
         induction q with
        | single _ => have h1 : multiply p1 (single _) = p1 := by sorry --apply mult_const p1
        | cons ex h1 h2 exy ih => 
         simp[homotopy.mult (ih p1 p2 h) ex h1 h2, multiply]-/


theorem homotopy_reducepath0 {G : Graph V E} {x y z : V} (ex : E) (h1 : G.init ex = x) (h2 : term G ex = y) (exy : EdgePath G y z) : homotopy (cons ex h1 h2 exy) (reducePath0 ex h1 h2 exy) := by
simp[homotopy, htclass]
cases exy with
| single y => 
    have : reducePath0 ex h1 h2 (single y) = cons ex h1 h2 (single y) := by rfl
    rfl
| cons ey h3 h4 eyz => apply
  if c : (x = term G ey) ∧ (ey = G.bar (ex)) then by
     let ih := Eq.symm (Eq.trans (And.left c) h4)
     cases ih with
     |refl =>
        have : basicht (ih ▸ eyz)  (cons ex h1 h2 (cons ey h3 h4 eyz))  := by 
          let j := @basicht.cancel V E G ex ey x y _ (ih ▸ eyz) h1 h2 (Eq.symm c.2)
          apply j
        have pr : (reducePath0 ex h1 h2 (cons ey h3 h4 eyz)).1 = (ih ▸ eyz) := by simp[reducePath0, c]
        let k := Quot.sound (Eq.symm pr ▸ this) 
        exact (Eq.symm k)
  else by
    have : reducePath0 ex h1 h2 (cons ey h3 h4 eyz) = cons ex h1 h2 (cons ey h3 h4 (eyz)) := by simp[reducePath0, c]
    simp [this]
 

theorem homotopy_reducepath {G : Graph V E} {x y : V} (p1 : EdgePath G x y): homotopy p1 (reducePath p1) := by
        induction p1 with
        | single x => 
          simp[homotopy, htclass]
          have h1 : ( @reducePath V E _ _ x x G (single x)).1 = single x  := by rfl
          have h2 : single x = (reducePath (single x)).1 := by exact (Eq.symm h1)
          apply Quot.sound (h2 ▸ basicht.consht x)

        | cons ex h1 h2 exy ih' => 
          let p3 := reducePath exy
          let q := p3.1
          let p4 := reducePath0 ex h1 h2 q
          have : p4.1 = (reducePath (cons ex h1 h2 exy)).1 := by rfl
          have t₁ : homotopy (cons ex h1 h2 q) (p4.1) := by apply homotopy_reducepath0 ex h1 h2 q
          have t₂ : homotopy exy q := by apply ih'
          have t₃ : homotopy (cons ex h1 h2 exy) (cons ex h1 h2 q) := by apply homotopy_left_mult_edge exy q t₂ ex h1 h2
          apply homotopy_trans (cons ex h1 h2 exy) (cons ex h1 h2 q) (reducePath (cons ex h1 h2 exy)) t₃ (this ▸ t₁)


