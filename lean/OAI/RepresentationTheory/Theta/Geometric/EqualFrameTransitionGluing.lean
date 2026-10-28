import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.UnitGluing
import OAI.RepresentationTheory.Theta.Geometric.OpenFrameScalars

/-! # Equal Frame Transition Gluing -/

namespace OAI.RepresentationTheory.Theta.Geometric.EqualFrameTransitionGluing

noncomputable section

/-! Two actual module sheaves with the same framed transition functions
are isomorphic. Overlap opens may be presented separately from intersections. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_iso_of_equal_frame_transitions {X : Scheme.{u}} (M N : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (W : ι → ι → X.Opens) (hl : ∀ i k, W i k ≤ U i) (hr : ∀ i k, W i k ≤ U k)
    (hw : ∀ i k, U i ⊓ U k ≤ W i k)
    (e : ∀ i, M.restrict (U i).ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme)
    (g : ∀ i, N.restrict (U i).ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme)
    (a : ∀ i k, Γ(X, W i k))
    (he : ∀ i k, (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hl i k) (e i)).hom =
      (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hr i k) (e k)).hom ≫
        AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((W i k).topIso.inv (a i k)))
    (hg : ∀ i k, (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hl i k) (g i)).hom =
      (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hr i k) (g k)).hom ≫
        AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((W i k).topIso.inv (a i k))) :
    Nonempty (M ≅ N) := by
  let b : ∀ i k, Γ(X, U i ⊓ U k) := fun i k => X.presheaf.map (homOfLE (hw i k)).op (a i k)
  apply IntrinsicFrame.UnitGluing.exists_iso_of_open_framed_units M N U hU e g (fun _ => 1) b b
  · intro i k
    have h := OpenFrameScalars.restrictOpenFrame_scalar M (hw i k) _ _ (a i k) (he i k)
    rw [AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp, AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp] at h
    exact h
  · intro i k
    have h := OpenFrameScalars.restrictOpenFrame_scalar N (hw i k) _ _ (a i k) (hg i k)
    rw [AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp, AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp] at h
    exact h
  · intro i k
    simp only [PowerGaugeCover.restrictRegularUnit, map_one, Units.val_one, mul_one, one_mul]

end

end OAI.RepresentationTheory.Theta.Geometric.EqualFrameTransitionGluing
