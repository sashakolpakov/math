import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalFiberTriviality
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldFrameReflection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Reduced Local Geometric Triviality -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalGeometricTriviality.Geometric

noncomputable section

/-! Geometric fiber trivializations suffice in the reduced local
triviality theorem. Reflection to each original residue-field fiber
uses its actual projective frame scheme and normalized section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

universe u
variable {S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
    [IsLocallyNoetherian S] [IsReduced S]
    {X : Over S} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) (s : S ⟶ X.left) (hs : s ≫ X.hom = 𝟙 S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

include P s hs r in
theorem reducedLocal_line_trivial_of_geometric_fibers
    (hL : ∀ y : S,
      let k := S.residueField y
      let c := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
      Nonempty ((Scheme.Modules.pullback
        (pullback.fst (X.hom.fiberToSpecResidueField y) c)).obj
        ((Scheme.Modules.pullback (X.hom.fiberι y)).obj L.sheaf) ≅
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback (X.hom.fiberToSpecResidueField y) c))) :
    Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) := by
  apply ReducedLocalFiberTriviality.Geometric.reducedLocal_line_trivial P s hs L r
  intro y
  let b := S.fromSpecResidueField y
  let f := X.hom.fiberι y
  let ρ := X.hom.fiberToSpecResidueField y
  have hp : IsPullback f ρ X.hom b := IsPullback.of_hasPullback X.hom b
  let sy := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection f ρ X.hom b hp s hs
  have hsy := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_snd f ρ X.hom b hp s hs
  have hxy := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_fst f ρ X.hom b hp s hs
  let ry := FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f sy b s hxy L.sheaf r
  let k := S.residueField y
  let c := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : IsProper ((Over.pullback b).obj X).hom :=
    inferInstanceAs (IsProper (pullback.snd X.hom b))
  have : Smooth ((Over.pullback b).obj X).hom :=
    inferInstanceAs (Smooth (pullback.snd X.hom b))
  have : GeometricallyConnected ((Over.pullback b).obj X).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd X.hom b))
  exact FieldFrameReflection.Geometric.field_line_trivial_of_cartesian_trivial
    (K := S.residueField y) (X := (Over.pullback b).obj X) (P.baseChange b) sy hsy (L.pullback f) ry
    (pullback.fst ρ c) (pullback.snd ρ c) c (IsPullback.of_hasPullback ρ c)
    (Classical.choice (hL y))

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalGeometricTriviality.Geometric
