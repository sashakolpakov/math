import OAI.RepresentationTheory.Theta.Geometric.FramedUnitGluing
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TwistOverFrames

/-! # Unit Gluing -/

namespace OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.UnitGluing

noncomputable section

/-! Gluing a regular-unit comparison directly from native restriction frames. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_iso_of_open_framed_units {X : Scheme.{u}} (M N : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme)
    (g : ∀ i, N.restrict (U i).ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme)
    (r : ∀ i, Γ(X, U i)ˣ) (a b : ∀ i k, Γ(X, U i ⊓ U k))
    (he : ∀ i k,
      (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U i ⊓ U k ≤ U i from inf_le_left) (e i)).hom =
      (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U i ⊓ U k ≤ U k from inf_le_right) (e k)).hom ≫
        AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((U i ⊓ U k).topIso.inv (a i k)))
    (hg : ∀ i k,
      (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U i ⊓ U k ≤ U i from inf_le_left) (g i)).hom =
      (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U i ⊓ U k ≤ U k from inf_le_right) (g k)).hom ≫
        AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((U i ⊓ U k).topIso.inv (b i k)))
    (hr : ∀ i k,
      a i k * (PowerGaugeCover.restrictRegularUnit (show U i ⊓ U k ≤ U i from inf_le_left) (r i) : Γ(X, U i ⊓ U k)) =
      (PowerGaugeCover.restrictRegularUnit (show U i ⊓ U k ≤ U k from inf_le_right) (r k) : Γ(X, U i ⊓ U k)) * b i k) :
    Nonempty (M ≅ N) := by
  have he' : ∀ i k, _ := fun i k =>
    AlgebraicGeometry.SheafCohomology.Projective.OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar M (U i ⊓ U k) _ _ (a i k) (he i k)
  have hg' : ∀ i k, _ := fun i k =>
    AlgebraicGeometry.SheafCohomology.Projective.OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar N (U i ⊓ U k) _ _ (b i k) (hg i k)
  simp only [AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization] at he' hg'
  obtain ⟨f, _⟩ := FramedUnitGluing.exists_iso_of_framed_units M N U hU
    (fun i => AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M (U i) (e i))
    (fun i => AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso N (U i) (g i)) r a b he' hg' hr
  exact ⟨f⟩

end

end OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.UnitGluing
