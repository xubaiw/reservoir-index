import Iris.BI.Classes
import Iris.BI.DerivedConnectives
import Iris.BI.DerivedLaws
import Iris.BI.Extensions
import Iris.BI.Interface
import Iris.Std.Classes

namespace Iris.BI
open Iris.Std
open BI

-- Persistent
instance purePersistent (φ : Prop) [BI PROP] :
  Persistent (PROP := PROP) `[iprop| ⌜φ⌝]
where
  persistent := by
    rw' [persistently_pure]

instance empPersistent [BI PROP] :
  Persistent (PROP := PROP) `[iprop| emp]
where
  persistent := persistently_emp_intro

instance andPersistent [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Persistent Q] →
  Persistent `[iprop| P ∧ Q]
where
  persistent := by
    rw' [persistently_and, !← persistent]

instance orPersistent [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Persistent Q] →
  Persistent `[iprop| P ∨ Q]
where
  persistent := by
    rw' [persistently_or, !← persistent]

instance existPersistent [BI PROP] (Ψ : α → PROP) :
  [∀ x, Persistent (Ψ x)] →
  Persistent `[iprop| ∃ x, Ψ x]
where
  persistent := by
    rw' [persistently_exist, ← persistent]

instance sepPersistent [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Persistent Q] →
  Persistent `[iprop| P ∗ Q]
where
  persistent := by
    rw' [← persistently_sep_2, !← persistent]

instance persistentlyPersistent [BI PROP] (P : PROP) :
  Persistent `[iprop| <pers> P]
where
  persistent := persistently_idemp_2

instance affinelyPersistent [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent `[iprop| <affine> P]
where
  persistent := by
    simp [bi_affinely, persistent]

instance affinelyIfPersistent (p : Bool) [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent `[iprop| <affine>?p P]
where
  persistent := by
    simp only [bi_affinely_if]
    cases p
    <;> simp [persistent]

instance intuitionisticallyPersistent [BI PROP] (P : PROP) :
  Persistent `[iprop| □ P]
where
  persistent := by
    simp [bi_intuitionistically, persistent]

instance absorbinglyPersistent [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent `[iprop| <absorb> P]
where
  persistent := by
    simp [bi_absorbingly, persistent]

instance absorbinglyIfPersistent (p : Bool) [BI PROP] (P : PROP) :
  [Persistent P] →
  Persistent `[iprop| <absorb>?p P]
where
  persistent := by
    simp only [bi_absorbingly_if]
    cases p
    <;> simp [persistent]

-- Affine
instance empAffine [BI PROP] :
  Affine (PROP := PROP) `[iprop| emp]
where
  affine := by
    simp

instance falseAffine [BI PROP] :
  Affine (PROP := PROP) `[iprop| False]
where
  affine := False_elim

instance andAffineL [BI PROP] (P Q : PROP) :
  [Affine P] →
  Affine `[iprop| P ∧ Q]
where
  affine := by
    rw' [affine, and_elim_l]

instance andAffineR [BI PROP] (P Q : PROP) :
  [Affine Q] →
  Affine `[iprop| P ∧ Q]
where
  affine := by
    rw' [affine, and_elim_r]

instance orAffine [BI PROP] (P Q : PROP) :
  [Affine P] →
  [Affine Q] →
  Affine `[iprop| P ∨ Q]
where
  affine := by
    apply or_elim
    <;> exact affine

instance forallAffine [Inhabited α] [BI PROP] (Φ : α → PROP) :
  [∀ x, Affine (Φ x)] →
  Affine `[iprop| ∀ x, Φ x]
where
  affine := by
    rw' [← affine (P := Φ default), forall_elim default]

instance existAffine [BI PROP] (Φ : α → PROP) :
  [∀ x, Affine (Φ x)] →
  Affine `[iprop| ∃ x, Φ x]
where
  affine := by
    apply exist_elim
    intro a
    exact affine

instance sepAffine [BI PROP] (P Q : PROP) :
  [Affine P] →
  [Affine Q] →
  Affine `[iprop| P ∗ Q]
where
  affine := by
    rw' [
      affine,
      (left_id : emp ∗ Q ⊣⊢ _),
      affine]

instance affinelyAffine [BI PROP] (P : PROP) :
  Affine `[iprop| <affine> P]
where
  affine := by
    simp [bi_affinely, affine]

instance affinelyIfAffine (p : Bool) [BI PROP] (P : PROP) :
  [Affine P] →
  Affine `[iprop| <affine>?p P]
where
  affine := by
    simp only [bi_affinely_if]
    cases p
    <;> simp [affine]

instance intuitionisticallyAffine [BI PROP] (P : PROP) :
  Affine `[iprop| □ P]
where
  affine := by
    simp [bi_intuitionistically, affine]

instance intuitionisticallyIfAffine (p : Bool) [BI PROP] (P : PROP) :
  [Affine P] →
  Affine `[iprop| □?p P]
where
  affine := by
    simp only [bi_intuitionistically_if]
    cases p
    <;> simp [affine]

-- Absorbing
instance pureAbsorbing (φ : Prop) [BI PROP] :
  Absorbing (PROP := PROP) `[iprop| ⌜φ⌝]
where
  absorbing := by
    rw' [absorbingly_pure]

instance andAbsorbing [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing `[iprop| P ∧ Q]
where
  absorbing := by
    rw' [absorbingly_and_1, !absorbing]

instance orAbsorbing [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing `[iprop| P ∨ Q]
where
  absorbing := by
    rw' [absorbingly_or, !absorbing]

instance forallAbsorbing [BI PROP] (Φ : α → PROP) :
  [∀ x, Absorbing (Φ x)] →
  Absorbing `[iprop| ∀ x, Φ x]
where
  absorbing := by
    rw' [absorbingly_forall Φ, absorbing]

instance existAbsorbing [BI PROP] (Φ : α → PROP) :
  [∀ x, Absorbing (Φ x)] →
  Absorbing `[iprop| ∃ x, Φ x]
where
  absorbing := by
    rw' [absorbingly_exist Φ, absorbing]

instance implAbsorbing [BI PROP] (P Q : PROP) :
  [Persistent P] →
  [Absorbing P] →
  [Absorbing Q] →
  Absorbing `[iprop| P → Q]
where
  absorbing := by
    apply impl_intro_l ?_
    rw' [
      persistent_and_affinely_sep_l,
      absorbingly_sep_r,
      ← persistent_and_affinely_sep_l,
      impl_elim_r,
      absorbing]

instance sepAbsorbingL [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  Absorbing `[iprop| P ∗ Q]
where
  absorbing := by
    rw' [← absorbingly_sep_l, absorbing]

instance sepAbsorbingR [BI PROP] (P Q : PROP) :
  [Absorbing Q] →
  Absorbing `[iprop| P ∗ Q]
where
  absorbing := by
    rw' [← absorbingly_sep_r, absorbing]

instance wandAbsorbingL [BI PROP] (P Q : PROP) :
  [Absorbing P] →
  Absorbing `[iprop| P -∗ Q]
where
  absorbing := by
    simp only [bi_absorbingly]
    apply wand_intro_l
    rw' [
      (assoc : P ∗ True ∗ (P -∗ Q) ⊣⊢ _),
      (sep_elim_l : P ∗ True ⊢ _),
      wand_elim_r]

instance wandAbsorbingR [BI PROP] (P Q : PROP) :
  [Absorbing Q] →
  Absorbing `[iprop| P -∗ Q]
where
  absorbing := by
    rw' [absorbingly_wand, (absorbing : _ ⊢ Q), (absorbingly_intro : _ ⊢ <absorb> P)]

instance absorbinglyAbsorbing [BI PROP] (P : PROP) :
  Absorbing `[iprop| <absorb> P]
where
  absorbing := by
    rw' [absorbingly_idemp]

instance persistentlyAbsorbing [BI PROP] (P : PROP) :
  Absorbing `[iprop| <pers> P]
where
  absorbing := by
    rw' [absorbingly_elim_persistently]

instance persistentlyIfAbsorbing [BI PROP] (P : PROP) (p : Bool) :
  [Absorbing P] →
  Absorbing `[iprop| <pers>?p P]
where
  absorbing := by
    simp only [bi_persistently_if]
    cases p
    <;> simp [absorbing]

section Affine

instance (priority := default + 10) biAffineAbsorbing [BIAffine PROP] (P : PROP) :
  Absorbing P
where
  absorbing := by
    simp only [bi_absorbingly]
    rw' [
      (affine : (True : PROP) ⊢ _),
      (left_id : emp ∗ P ⊣⊢ _)]

end Affine
end Iris.BI
