import OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoPrimeTorsion
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Single Prime -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SinglePrime.SinglePrimeTorsion

noncomputable section

/-! A sheaf reduction sequence with surjective global sections gives torsion-free degree-one sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable (p : ℕ) [Fact p.Prime] (X : TopCat.{0})

local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.Sheaves ℤ_[p] X
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.coefficient ℤ_[p] X

local instance : HasDerivedCategory.{1} V := HasDerivedCategory.standard _

theorem torsionFree (M N : V) (r : M ⟶ N)
    (hz : ((p : ℤ_[p]) • 𝟙 M) ≫ r = 0)
    (he : (ShortComplex.mk ((p : ℤ_[p]) • 𝟙 M) r hz).ShortExact)
    (hf : Function.Surjective (r.hom.app (op ⊤))) :
    Module.IsTorsionFree ℤ_[p]
      ((DerivedCategory.singleFunctor V 0).obj A ⟶
        (DerivedCategory.Q.obj (((CochainComplex.single₀ V).obj M).extend
          ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧) := by
  let F := CochainComplex.single₀ V
  have hfirst : F.map ((p : ℤ_[p]) • 𝟙 M) = (p : ℤ_[p]) • 𝟙 (F.obj M) := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero =>
      change ((CochainComplex.single₀ V).map ((p : ℤ_[p]) • 𝟙 M)).f 0 = _
      rw [CochainComplex.single₀_map_f_zero]
      rfl
    | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 M (n + 1) (by omega)).eq_of_tgt _ _
  have hzF : ((p : ℤ_[p]) • 𝟙 (F.obj M)) ≫ F.map r = 0 := by
    rw [← hfirst, ← F.map_comp, hz, F.map_zero]
  have e : (ShortComplex.mk ((p : ℤ_[p]) • 𝟙 (F.obj M)) (F.map r) hzF) ≅
      (ShortComplex.mk ((p : ℤ_[p]) • 𝟙 M) r hz).map F :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        change 𝟙 _ ≫ F.map ((p : ℤ_[p]) • 𝟙 M) = ((p : ℤ_[p]) • 𝟙 (F.obj M)) ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
        exact hfirst)
      (by
        change 𝟙 _ ≫ F.map r = F.map r ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id])
  have heF := (ShortComplex.shortExact_iff_of_iso e).mpr (he.map_of_exact F)
  apply First.TwoPrimeTorsion.FirstTwoComplex.torsionFree p X (F.obj M) (F.obj N) (F.map r) hzF
  · intro n _
    exact (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp heF n
  · change Function.Surjective ((((CochainComplex.single₀ V).map r).f 0).hom.app (op ⊤))
    erw [CochainComplex.single₀_map_f_zero]
    exact hf
  · intro x
    change (((CochainComplex.single₀ V).obj M).d 0 1).hom.app (op ⊤) x = 0
    rw [HomologicalComplex.single_obj_d]
    rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SinglePrime.SinglePrimeTorsion
