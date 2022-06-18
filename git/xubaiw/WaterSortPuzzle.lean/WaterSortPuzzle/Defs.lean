import Mathlib.Data.List.Perm
import WaterSortPuzzle.Utils

namespace WaterSortPuzzle

/-!
# 水排序拼图的问题定义
-/

/-!
## 定义：颜色
-/

abbrev Color (m : Nat) := Fin m

/-!
## 定义：试管
-/

structure Tube (m h : Nat) where
  val : List (Color m)
  h_volume : val.length ≤ h

namespace Tube

variable (t : Tube m h)

def length : Nat := t.val.length

def sameColorAux : List (Color m) → Prop
| [] => True
| [_] => true
| c₁ :: c₂ :: cs => c₁ = c₂ ∧ sameColorAux (c₂ :: cs)

def sameColor : Prop := sameColorAux t.val

def isEmpty : Prop := t.val = []

instance : Decidable t.isEmpty := 
  if h : t.val = [] then isTrue h else isFalse h

def isFull : Prop := t.length = h

instance : Decidable t.isFull := 
  if h' : t.length = h then isTrue h' else isFalse h'

def topColor (h : ¬t.isEmpty) : Color m := 
  match h' : t.val with
  | [] => absurd h' h
  | c :: cs => c

def topColor? : Option (Color m) :=
  if h : t.isEmpty then none else topColor t h

def empty : Tube m h := ⟨ [], by simp ⟩ 

def fullSameColor (i : Fin m) : Tube m h := ⟨ List.replicate h i, by simp ⟩ 

end Tube

/-!
## 定义：试管组

关键类型：

- `ColorPerm`: 试管颜色打乱的命题。
- `ColorComplete`: 试管颜色完备的命题。
- `Tubes`: 试管组
-/

/--
实际上是二维列表的打乱，因而在符号上选择 `~²`
-/
def colorPerm (ts₁ ts₂ : List (Tube m h)) : Prop :=
  let f₁ := ts₁.map Tube.val |>.join
  let f₂ := ts₂.map Tube.val |>.join
  f₁ ~ f₂

infixl:50 " ~² " => colorPerm

theorem colorPerm.mod_h :
  ∀ {ts₁ ts₂ : List (Tube m h)} {i : Fin m}, ts₁ ~² ts₂ →
    let f₁ := ts₁.map Tube.val |>.join ;
    let f₂ := ts₂.map Tube.val |>.join ;
    (f₁.count i) % h = (f₂.count i) % h := by
  intro ts₁ ts₂ i h
  simp_all [List.join, List.count, List.countp, colorPerm]

/--
试管颜色是否完备。有三种不同情况：

- 空列表 是完备的
- 完备列表 加上 装满同一种颜色的试管 是完备的
- 完备列表 打乱颜色顺序是完备的
-/
inductive ColorComplete : List (Tube m h) → Prop
| nil : ColorComplete []
| cons : ColorComplete ts → ColorComplete ((.fullSameColor i)::ts)
| perm : ColorComplete ts → ts ~² ts' → ColorComplete ts'

theorem ColorComplete.mod_h : ∀ {ts : List (Tube m h)}, ColorComplete ts → 
  let f := ts.map Tube.val |>.join ;
  ∀ i : Fin m, (f.count i) % h = 0 := by
    intro ts colorComplete_ts
    simp
    induction colorComplete_ts <;> simp [List.count_join]
    . intro i
      exact Nat.zero_mod h
    . rename_i a b c d
      intro i
      sorry
    . sorry


structure Tubes (m h n : Nat) where
  val : List (Tube m h)
  h_num : val.length = n
  h_colorComplete : ColorComplete val

namespace Tubes

variable (ts : Tubes m h n)

def length := ts.val.length

instance : Membership (Tube m h) (Tubes m h n) where
  mem t ts := t ∈ ts.val

def sorted : Prop :=
  ∀ t, t ∈ ts → t.sameColor ∧ t.isFull

def get (m : Fin n) :=
  have m : Fin ts.val.length := by
    rw [ts.h_num]
    assumption
  ts.val.get m

def set (i : Fin n) (t : Tube m h) (hc : ColorComplete (ts.val.set i t)) : Tubes m h n :=
  { 
    val := ts.val.set i t
    h_num := by
      rw [List.length_set ts.val i t, ts.h_num]
    h_colorComplete := hc
  }

end Tubes

/-!
## 定义：倾倒过程
-/

/-- 描述倾倒过程 -/
structure PourStep (n : Nat) where
  source : Fin n
  sink : Fin n

/-- 进行一次倾倒 -/
def PourStep.pour (ts : Tubes m h n) (s : PourStep n) : Tubes m h n :=
  let t₁ := ts.get s.source
  let t₂ := ts.get s.sink
  let (t₁', t₂') := match t₁, t₂ with
  | ⟨[], _⟩ , _ => (t₁, t₂)
  | ⟨c::cs, h₁⟩ , ⟨[], h₂⟩ => 
    -- 一些定理证明
    have hc : (c::cs).length > 0  := cs.length_cons_gt_zero c
    have hgt : h > 0              := Nat.lt_of_lt_of_le hc h₁
    have hge : h ≥ 1              := Nat.ge_one_of_gt_zero hgt
    have hlt : cs.length < h      := Nat.lt_of_lt_of_le (cs.length_cons_lt c) h₁
    have hle : cs.length ≤ h      := Nat.le_of_lt hlt
    have hle' : [c].length ≤ h    := hge
    (⟨cs, hle⟩, ⟨[c], hle'⟩)
  | ⟨c₁::cs₁, h₁⟩, ⟨c₂::cs₂, h₂⟩ =>
    if c₁ = c₂ then
      if h' : (c₂::cs₂).length + 1 ≤ h then
        -- 一些定理证明
        have hlt : cs₁.length < h             := Nat.lt_of_lt_of_le (cs₁.length_cons_lt c₁) h₁
        have hle : cs₁.length ≤ h             := Nat.le_of_lt hlt
        have hle' : (c₁::c₂::cs₂).length ≤ h  := by simp only [List.length_cons c₁ (c₂::cs₂), h']
        (⟨cs₁, hle⟩, ⟨c₁::c₂::cs₂, hle'⟩)
      else 
        (⟨c₁::cs₁, h₁⟩, ⟨c₂::cs₂, h₂⟩)
    else 
      (⟨c₁::cs₁, h₁⟩, ⟨c₂::cs₂, h₂⟩)
  ts
  |>.set s.source t₁' (by sorry)
  |>.set s.sink t₂' sorry
  
/-- 进行一系列倾倒过程 -/
def Tubes.apply (ts : Tubes m h n) (ss : List (PourStep n)) : Tubes m h n :=
  ss.foldl (λ acc s => s.pour acc) ts

/-!
## 定义：水排序问题

关键类型：

- `Puzzle`: 问题的定义，包括 初始状态及约束、空试管数量 等配置。
- `Solution`: 问题的解，包含一系列步骤，以及正确性证明。

目标即为寻找到一个函数具有 `(p : Puzzle m h n) → Solution p` 的类型。
-/

/-- 问题定义 -/
structure Puzzle (m h n : Nat) where
  /-- 初始状态 -/
  initial : Tubes m h n
  /-- 空试管的数量 -/
  k : Nat := 0
  /-- 初始状态要求所有试管为满的 -/
  h_full : ∀ t, t ∈ initial → t.isFull

/-- 问题解的定义 -/
structure Solution (p : Puzzle m h n) where
  /-- 一系列解的步骤 -/
  steps : List (PourStep n)
  /-- 正确性证明 -/
  h_sorted : (p.initial.apply steps).sorted

end WaterSortPuzzle
