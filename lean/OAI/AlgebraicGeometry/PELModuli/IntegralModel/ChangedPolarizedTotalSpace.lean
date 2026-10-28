import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AffineFamilyNeighborhoods
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.NeighborhoodPullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization

/-! # Changed Polarized Total Space -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChangedPolarizedTotalSpace

noncomputable section

/-! Affine neighborhoods for the literal scalar change of a polarized
family's total space. The comparison with relative family pullback is
the actual Cartesian base-change square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem baseChanged_polarized_totalSpace_affine_neighborhoods
    {R K : Type} [CommRing R] [Field K] [Infinite K] (φ : R →+* K)
    (X : Over (Spec (.of R)))
    [IsLocallyNoetherian ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left]
    (hAF : ∀ F : Set ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left,
      F.Finite → ∃ V : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left.Opens,
        IsAffineOpen V ∧ F ⊆ V)
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N X.left) :
    let Y : Over (Spec (.of R)) := Over.mk (A.abelian.scheme.hom ≫ X.hom)
    ∀ F : Set ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left,
      F.Finite → ∃ V : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left.Opens,
        IsAffineOpen V ∧ F ⊆ V := by
  let b := Spec.map (CommRingCat.ofHom φ)
  let Y : Over (Spec (.of R)) := Over.mk (A.abelian.scheme.hom ≫ X.hom)
  let a : Y ⟶ X := Over.homMk A.abelian.scheme.hom rfl
  let X' := (Over.pullback b).obj X
  let p := pullback.fst X.hom b
  let e := (Specialization.base_change_square b a).isoPullback
  have hA := Polarized.AffineFamilyNeighborhoods.polarized_family_finite_set_affine_neighborhood X'.hom hAF (A.pullback p)
  exact Affine.NeighborhoodPullback.finite_set_affine_neighborhood_of_affine e.hom hA

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChangedPolarizedTotalSpace
