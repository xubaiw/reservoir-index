import SciLean.Core.Fun.Diff

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] 
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

noncomputable 
def fwdDiff (f : X → Y) : X → Y×(X → Y) := λ x => (f x, λ dx => δ f x dx)

prefix:max "𝓣" => fwdDiff

def fwdDiff.split (f : α → β × γ) : (α → β)×(α→γ) := (λ a => (f a).1, λ a => (f a).2)
def fwdDiff.merge (fg : (α → β)×(α→γ)) : α → β×γ := λ a => (fg.1 a, fg.2 a) 
def fwdDiff.transpose : (Y₁×Y₁)×(Y₂×Y₂) → (Y₁×Y₂)×(Y₁×Y₂) := λ ((a,b),(c,d)) => ((a,c),(b,d))

theorem fwdDiff_of_linear (f : X → Y) [IsLin f] : fwdDiff f = λ x => (f x, f) :=
by 
  simp [fwdDiff]
  rw[diff_of_linear]
  done

def fmapFD {α : Type} (f : X×(α → X) → Y×(α → Y)) (g : X×(α → X) → Z×(α → Z))
  : X×(α → X) → (Y×Z)×(α → Y×Z)
  :=
  λ xdx =>
    let (y,dy) := f xdx
    let (z,dz) := g xdx
    ((y, z), λ a => (dy a, dz a))

-- Computale version of `fwdDiff eval` where you specify the `Tf = fwdDiff f` explicitely
def evalFD {α : Type} (fxdfdx : ((X → Y) × X) × (α → (X → Y) × X)) (Tf : (X × (α → X)) → (Y × (α → Y)))
  : Y × (α → Y)
  := 
  let ((f,x),dfdx) := fxdfdx
  let (y, dy) := Tf (x, λ a => (dfdx a).2)
  (y, λ a => (dfdx a).1 x + dy a)

-- @[simp ↓]
-- theorem eval_fwdDiff (f : X → Y) [IsSmooth f] (x : X) (dfdx : α → (X → Y) × X)
--   : fwdDiff α (λ ((f,x) : (X → Y) × X) => f x) ((f,x),dfdx) = evalFD ((f,x),dfdx) (fwdDiff α f)
--   :=
-- by
--   simp[fwdDiff,evalFD] done

def uncurryFD {α : Type} (Tf : X×(α → X) → (Y→Z)×(α → Y → Z)) (Tfx : X → Y×(α → Y) → Z×(α → Z)) 
  : (X×Y)×(α → X×Y) → Z×(α → Z)
  :=
  λ ((x, y), dxy) =>
    let (fx, df) := Tf (x, λ a => (dxy a).1)
    let (z, dfx) := Tfx x (y, λ a => (dxy a).2)
    (z, λ a => df a y + dfx a)

-- @[simp ↓]
-- theorem uncurry_fwdDiff (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
--   : fwdDiff α (Function.uncurry f) = uncurryFD (fwdDiff α f) (λ x => fwdDiff α (f x))
--   := by
--   simp[fwdDiff,Function.uncurry,uncurryFD] done

----------------------------------------------------------------------

@[simp ↓, simp_diff]
theorem id.arg_x.fwdDiff_simp
  : fwdDiff (λ x : X => x) = λ x => (x, λ dx => dx) := by simp[fwdDiff] done

@[simp ↓, simp_diff]
theorem const.arg_y.fwdDiff_simp (x : X)
  : fwdDiff (λ y : Y => x) = λ y => (x, λ _ => 0) := by simp[fwdDiff] done

@[simp ↓ low-3]
theorem swap.arg_x.fwdDiff_simp (f : α → X → Y) [∀ i, IsSmooth (f i)]
  : fwdDiff (λ x a => f a x) = 
           λ x => 
           let f' := λ a => fwdDiff (f a)
           (λ a => f a x, λ dx a => (f' a x).2 dx) := 
by 
  simp[fwdDiff] done
/-
-- @[simp ↓ low-2, simp_diff low-2]
theorem scomb.arg_x.fwdDiff_simp
  (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
  (g : X → Y) [IsSmooth g] 
  : fwdDiff (λ x => f x (g x))
    = 
    λ xdx =>
      let Tf  := fwdDiff f
      let Tg  := fwdDiff g
      let Tfg := fmapFD Tf Tg
      let Tfx := fwdDiff α (f xdx.1)
      evalFD (fmapFD Tf Tg xdx) Tfx
    := 
  by 
    simp[fwdDiff,fmapFD,evalFD] done

@[simp ↓ low-2, simp_diff low-2]
theorem scomb.arg_x.fwdDiff_simp_alt
  (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
  (g : X → Y) [IsSmooth g] 
  : fwdDiff α (λ x => f x (g x))
    = 
    λ xdx =>
      let Tidg := fmapFD id (fwdDiff α g)
      let Tf   := fwdDiff α f
      let Tfx  := λ x => fwdDiff α (f x)
      let Tuncurryf := uncurryFD Tf Tfx
      Tuncurryf (Tidg xdx)
  := 
by 
  simp[fwdDiff,uncurryFD,fmapFD,evalFD] done

@[simp ↓ low-1, simp_diff low-1]
theorem comp.arg_x.fwdDiff_simp
  (f : Y → Z) [IsSmooth f] 
  (g : X → Y) [IsSmooth g] 
  : fwdDiff α (λ x => f (g x)) 
    = 
    λ xdx => fwdDiff α f (fwdDiff α g xdx) 
  := 
by 
  simp[fwdDiff, uncurryFD, fmapFD] done

@[simp ↓ low, simp_diff low]
theorem parm.arg_x.fwdDiff_simp
  (f : X → α → Y) [IsSmooth f] (a : α)
  : fwdDiff β (λ x => f x a) = λ xdx => 
      let (f,df) := fwdDiff β f xdx
      (f a, λ b => df b a)
  := 
by 
  simp [fwdDiff] done
-/
