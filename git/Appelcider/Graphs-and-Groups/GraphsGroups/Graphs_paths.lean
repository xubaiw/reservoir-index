structure Graph(V: Type) (E: Type) where
  null : E
  init : E → V
  bar : E → E
  barInv : bar ∘ bar = id
  barNoFP : ∀ e: E, bar e ≠ e
  
variable {V: Type}{E: Type}[DecidableEq V][DecidableEq E]

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

-- proves associativity of path multiplication
theorem mult_assoc {G : Graph V E} (p : EdgePath G w x) (q : EdgePath G x y) (r : EdgePath G y z):
      (multiply (multiply p q) r) = (multiply p (multiply q r)) := by
      induction p with
      | single w => simp[multiply]
      | cons ex h1 h2 exy ih => simp[multiply, ih]

theorem mult_const {G : Graph V E} {p : EdgePath G x y} : 
      (multiply p (single y)) = p := by
      induction p with
      | single x => simp [multiply] 
      | cons ex h1 h2 exy ih => simp[multiply, ih] 

-- reverses an edgepath
def inverse {G : Graph V E} {x y : V}: (EdgePath G x y) → (EdgePath G y x)
| single x => single x 
| cons ex h1 h2 exy => multiply (inverse exy) (cons (G.bar (ex)) h2 (lemma1 h1) (single x)) 

def reducePath0 {G : Graph V E} {x y : V}: (p : EdgePath G x y) →  { rp : EdgePath G x y // rp.length ≤ p.length} 
| single x => ⟨ single x, by simp⟩ 
| cons ex h1 h2 exy => by
 cases exy with
 | single x => exact ⟨cons ex h1 h2 (single y), by simp⟩ 
 | cons ey h3 h4 eyz => 
   apply
  if c : (x = term G ey) ∧ (ey = G.bar (ex)) then
  ⟨ Eq.symm (Eq.trans (And.left c) h4) ▸ eyz, by 
      have h5 : (Eq.symm (Eq.trans (And.left c) h4) ▸ eyz).length = eyz.length := by sorry
      simp[EdgePath.length, h5, Nat.le_trans (Nat.le_succ (length eyz)) (Nat.le_succ (length eyz +1))]
  ⟩ 
  else
  ⟨ cons ex h1 h2 (cons ey h3 h4 (eyz)), by sorry⟩ 

-- reduces given path such that no two consecutive edges are inverses of each other
def reducePath {G : Graph V E} : (p : EdgePath G x y ) → 
  {rp : EdgePath G x y // rp.length ≤ p.length} 
| single x => ⟨single x, by simp⟩
| cons ex h1 h2 ey'y => 
  have h5': length ey'y < length (cons ex h1 h2 ey'y) := by simp[EdgePath.length, Nat.lt_succ_self]
  let ⟨ey'z, ih1⟩ := reducePath ey'y 
  let ⟨ ez, ih⟩ := reducePath0 (cons ex h1 h2 ey'z) 
  ⟨ ez , by sorry ⟩ 
termination_by _ _ _ _ p => p.length



--defines homotopy of edgepaths
inductive homotopy {G : Graph V E} : EdgePath G x y → EdgePath G x y → Sort where
| consht : (x : V) → (homotopy (single x) (single x)) -- constant homotopy
| cancel : (ex : E) → {w x y : V} → (p : EdgePath G x y) → -- cancelling consecutive opposite edges from a path
           (h : G.init ex = x) → { h1 : term G ex = w} → 
           homotopy p (cons ex h h1 (cons (G.bar (ex)) h1 (lemma1 h) p))
| mult : {x y z : V} → {p q : EdgePath G y z} →   -- adding an edge to homotopic paths
         homotopy p q → (ex : E) →(h1 : G.init ex = x) → ( h : term G ex = y)→ 
         homotopy (cons ex h1 h p) (cons ex h1 h q)

--proves that homotopy is left multiplicative
theorem homotopy_left_mult {G : Graph V E} {x y z : V} (p1 p2 : EdgePath G y z) (q : EdgePath G x y) (h :homotopy p1 p2):
         (homotopy (multiply q p1) (multiply q p2)) := by
         induction q with
        | single w  => 
          simp [multiply, h]
        | cons ex h1 h2 exy ih => 
         simp[homotopy.mult (ih p1 p2 h) ex h1 h2, multiply]

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



/-theorem homotopy_reducepath {G : Graph V E} {x y : V} (p1 p2 : EdgePath G x y) (ih : p2.length ≤ p1.length)
        (h : (reducePath p1).1 = p2) : homotopy p1 p2 := by
        induction p1 with
        | single x => 
          have h1 : ( @reducePath V E _ _ x x G (single x)).1 = single x  := by rfl
          have h2 : single x = p2 := by simp[(Eq.symm h1), h]
          have h3 : @homotopy V E G x x (single x) (single x) := by exact homotopy.consht x
          exact h2 ▸ h3
        | cons ex h1 h2 exy ih' => 
          have h1' : homotopy (reducePath exy) exy := by sorry
          let p3 := @reducePath0 V E _ _ G _ _ (cons ex h1 h2 (reducePath exy).1)
          have h2' : homotopy p3.1 (cons ex h1 h2 (reducePath exy).1) := by sorry
          have h3' : (@reducePath V E _ _ _ _ G (cons ex h1 h2 exy)).1 = p3.1 := by rfl
-/

