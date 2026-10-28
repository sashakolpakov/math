import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.BaseChangeMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.PullbackRange

/-! # Clopen Cover Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenCoverBaseChange.BundleCycles

noncomputable section

/-! Disjoint open and closed covers remain disjoint covers after arbitrary
scheme base change, using the actual pullback maps. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X Y : Scheme.{0}} (p : E ⟶ X) {ι : Type} (U : ι → Scheme.{0})
    (i : ∀ k, U k ⟶ E) [∀ k, IsOpenImmersion (i k)] [∀ k, IsClosedImmersion (i k)]
    (b : Y ⟶ X)

instance clopenCoverBaseChangeMap_isOpenImmersion (k : ι) :
    IsOpenImmersion (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap p (i k ≫ p) (i k) rfl b) :=
  MorphismProperty.of_isPullback
    (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_isPullback p (i k ≫ p) (i k) rfl b).flip inferInstance

omit [∀ (k : ι), IsOpenImmersion (i k)] [∀ (k : ι), IsClosedImmersion (i k)] in
theorem clopenCoverBaseChangeMap_range (k : ι) :
    Set.range (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap p (i k ≫ p) (i k) rfl b) =
      (pullback.fst p b) ⁻¹' Set.range (i k) := by
  have h := Scheme.image_preimage_eq_of_isPullback
    (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_isPullback p (i k ≫ p) (i k) rfl b).flip Set.univ
  simpa only [Set.preimage_univ, Set.image_univ] using h

omit [∀ (k : ι), IsOpenImmersion (i k)] [∀ (k : ι), IsClosedImmersion (i k)] in
theorem clopenCoverBaseChange_covers (hcover : ∀ x : E, ∃! k, x ∈ Set.range (i k)) :
    ∀ x : (pullback p b : Scheme),
      ∃! k, x ∈ Set.range (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap p (i k ≫ p) (i k) rfl b) := by
  intro x
  simpa only [clopenCoverBaseChangeMap_range, Set.mem_preimage] using hcover (pullback.fst p b x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenCoverBaseChange.BundleCycles
