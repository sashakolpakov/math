import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeProjectiveEquations
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameClassification
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Reduced Local Fiber Triviality -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalFiberTriviality.Geometric

noncomputable section

/-! On a reduced local base, an actual normalized line on a smooth
projective connected family is trivial if its residue-field fibers are
trivial. The proved frame-equation factory makes the frame projection
a closed immersion; fiber frames make it surjective. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
    [IsLocallyNoetherian S] [IsReduced S]
    {X : Over S} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) (s : S ⟶ X.left) (hs : s ≫ X.hom = 𝟙 S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (hL : ∀ y : S, Nonempty ((Scheme.Modules.pullback (X.hom.fiberι y)).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (X.hom.fiber y)))

include P hL s hs r in
theorem reducedLocal_rigidifiedFrame_isIso
    (D : FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation X.hom L.sheaf) :
    IsIso (D.rigidifiedFrameScheme s hs r).hom := by
  obtain ⟨e₀⟩ := hL (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint S)
  obtain ⟨n, v, _hn, _hv, ⟨e⟩⟩ :=
    RelativeProjectiveEquations.Geometric.exists_relativeProjective_frame_equations X.hom P s hs L r e₀ D
  let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  let : IsClosedImmersion (D.rigidifiedFrameScheme s hs r).hom := by
    rw [← e.hom.w]
    infer_instance
  let : Surjective (D.rigidifiedFrameScheme s hs r).hom := by
    constructor
    intro y
    obtain ⟨ey⟩ := hL y
    obtain ⟨q⟩ := RelativeFrameClassification.Geometric.relativeProjective_rigidifiedFrame_hasPoint_of_trivialization P s hs D r
      (X.hom.fiberι y) (X.hom.fiberToSpecResidueField y) (S.fromSpecResidueField y)
      (IsPullback.of_hasPullback X.hom (S.fromSpecResidueField y)) ey.symm
    refine ⟨q.left (default : Spec (S.residueField y)), ?_⟩
    have hw := congrArg (fun f : Spec (S.residueField y) ⟶ S => f default) q.w
    exact hw.trans (Scheme.fromSpecResidueField_apply y default)
  exact isIso_of_isClosedImmersion_of_surjective _

include P hL s hs r in
theorem reducedLocal_line_trivial : Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) := by
  let D := FormalGeometry.Completion.Projective.LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L
  let := reducedLocal_rigidifiedFrame_isIso P s hs L r hL D
  let q : Over.mk (𝟙 S) ⟶ D.rigidifiedFrameScheme s hs r :=
    Over.homMk (inv (D.rigidifiedFrameScheme s hs r).hom) (IsIso.inv_hom_id _)
  have hp : IsPullback (𝟙 X.left) X.hom X.hom (𝟙 S) := IsPullback.of_id_fst
  have hc := (RelativeFrameClassification.Geometric.relativeProjective_rigidifiedFrame_hasPoint_iff_trivialClass P s hs D r
    (𝟙 X.left) X.hom (𝟙 S) hp).mp ⟨q⟩
  rw [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] at hc
  exact Quotient.exact hc

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalFiberTriviality.Geometric
