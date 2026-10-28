/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafDifferential.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafCofaces

/-! # Sheaf Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafDifferential.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X) (n : ℕ)

/-- The differential in the sheaf-level Cech resolution. -/
noncomputable def cechDifferential :
    IntrinsicCech.SheafTerms.cechTerm F U n ⟶ IntrinsicCech.SheafTerms.cechTerm F U (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • SheafCofaces.IntrinsicCech.cechCoface F U n k

theorem sheaf_sum_apply_finset {A B : TopCat.Sheaf AddCommGrpCat.{u} X}
    {κ : Type*} (s : Finset κ) (f : κ → (A ⟶ B)) (V : (Opens X)ᵒᵖ)
    (x : A.obj.obj V) :
    (∑ i ∈ s, f i).hom.app V x = ∑ i ∈ s, (f i).hom.app V x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change (f a).hom.app V x + (∑ i ∈ s, f i).hom.app V x = _
      rw [ih]

theorem sheaf_sum_apply {A B : TopCat.Sheaf AddCommGrpCat.{u} X}
    {κ : Type*} [Fintype κ] (f : κ → (A ⟶ B)) (V : (Opens X)ᵒᵖ)
    (x : A.obj.obj V) :
    (∑ i, f i).hom.app V x = ∑ i, (f i).hom.app V x :=
  sheaf_sum_apply_finset Finset.univ f V x

/-- Under the concrete section equivalence, the sheaf-level Cech differential is the
alternating sum of tuple-deletion restrictions. -/
theorem cechDifferential_apply (V : Opens X)
    (x : (IntrinsicCech.SheafTerms.cechTerm F U n).obj.obj (op V)) (i : Fin (n + 2) → ι) :
    IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V
        ((cechDifferential F U n).hom.app (op V) x) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (homOfLE (inf_le_inf_left V
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
          (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n V x
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) := by
  rw [cechDifferential]
  calc
    _ = IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V
        (∑ k : Fin (n + 2),
          ((-1 : ℤ) ^ (k : ℕ) • SheafCofaces.IntrinsicCech.cechCoface F U n k).hom.app (op V) x) i :=
      congrArg (fun y => IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V y i)
        (sheaf_sum_apply _ (op V) x)
    _ = (∑ k : Fin (n + 2),
        IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V
          (((-1 : ℤ) ^ (k : ℕ) • SheafCofaces.IntrinsicCech.cechCoface F U n k).hom.app (op V) x)) i := by
      rw [map_sum]
    _ = ∑ k : Fin (n + 2),
        IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V
          (((-1 : ℤ) ^ (k : ℕ) • SheafCofaces.IntrinsicCech.cechCoface F U n k).hom.app (op V) x) i :=
      Finset.sum_apply i Finset.univ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      change IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U (n + 1) V
          ((-1 : ℤ) ^ (k : ℕ) • ((SheafCofaces.IntrinsicCech.cechCoface F U n k).hom.app (op V) x)) i = _
      rw [map_zsmul, Pi.smul_apply, SheafCofaces.IntrinsicCech.cechCoface_apply]
      exact congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • y)
        (ConcreteCategory.congr_hom
          (congrArg F.obj.map (Subsingleton.elim _ _))
          (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n V x
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafDifferential.IntrinsicCech
