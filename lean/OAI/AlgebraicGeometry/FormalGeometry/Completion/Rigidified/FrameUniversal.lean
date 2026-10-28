import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification

/-! # Frame Universal -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! Maps to the normalized-frame scheme give actual normalized frames
on every Cartesian test family, without an affineness restriction. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
  {Y T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ π g)
  (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
  (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrameToNormalizedTrivialization (p : Over.mk g ⟶ D.rigidifiedFrameScheme s hs r) :
    { e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf //
      Rigidified.FrameScalar.Construction.frameAxisScalar f (NormalizedFrameClassification.Construction.cartesianSection f ρ π g hp s hs) g s
        (NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π g hp s hs) L.sheaf r e = 1 } :=
  ⟨D.classifiedFramePullback f ρ g hp (D.rigidifiedFramePointEquiv s hs r (Over.mk g) p).val,
    (D.classifiedFramePullback_scalar f ρ g hp (D.rigidifiedFramePointEquiv s hs r (Over.mk g) p).val
      s hs (NormalizedFrameClassification.Construction.cartesianSection f ρ π g hp s hs) (NormalizedFrameClassification.Construction.cartesianSection_snd f ρ π g hp s hs)
        (NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π g hp s hs) r).trans
          (D.rigidifiedFramePointEquiv s hs r (Over.mk g) p).property⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
