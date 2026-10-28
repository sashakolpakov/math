import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.NeighborhoodPullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization

/-! # Etale Cover Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleCoverBaseChange

noncomputable section

/-! The base change of a finite etale cover inherits reducedness,
separatedness, and affine neighborhoods of finite subsets. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem finite_etale_cover_baseChange_geometry {R K : Type} [CommRing R] [Field K]
    (φ : R →+* K) {X Y : Over (Spec (.of R))} (f : X ⟶ Y)
    [IsFinite f.left] [Etale f.left]
    (hred : IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left)
    (hsep : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left.IsSeparated)
    (hAF : ∀ F : Set ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left,
      F.Finite → ∃ V : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left.Opens,
        IsAffineOpen V ∧ F ⊆ V) :
    IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left ∧
    ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left.IsSeparated ∧
    (∀ F : Set ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left,
      F.Finite → ∃ V : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left.Opens,
        IsAffineOpen V ∧ F ⊆ V) := by
  let b := Spec.map (CommRingCat.ofHom φ)
  let f' := ((Over.pullback b).map f).left
  have : IsFinite f' := MorphismProperty.of_isPullback (Specialization.base_change_square b f)
    (inferInstanceAs (IsFinite f.left))
  have : Etale f' := MorphismProperty.of_isPullback (Specialization.base_change_square b f)
    (inferInstanceAs (Etale f.left))
  have : IsReduced ((Over.pullback b).obj Y).left := hred
  have : ((Over.pullback b).obj Y).left.IsSeparated := hsep
  refine ⟨EtaleReduced.finite_etale_isReduced f', ?_, Affine.NeighborhoodPullback.finite_set_affine_neighborhood_of_affine f' hAF⟩
  constructor
  rw [← terminal.comp_from f']
  infer_instance

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleCoverBaseChange
