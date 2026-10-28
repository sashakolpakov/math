import OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints
import OAI.AlgebraicGeometry.Foundations.Scheme.ComplexPointExistence
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Complex Closed Image Disjointness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComplexClosedImageDisjointness

noncomputable section

/-! Disjoint native complex-point images of closed finite-type
subschemes are disjoint as actual scheme images. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem closed_complex_images_disjoint {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (f : Y ⟶ X) (g : Z ⟶ X) [IsClosedImmersion f.left] [IsClosedImmersion g.left]
    (h : ∀ (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z), y ≫ f ≠ z ≫ g) :
    Disjoint (Set.range f.left) (Set.range g.left) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply Set.disjoint_left.mpr
  intro x hxf hxg
  have hc : IsClosed (Set.range f.left ∩ Set.range g.left) :=
    f.left.isClosedEmbedding.isClosed_range.inter g.left.isClosedEmbedding.isClosed_range
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (X := X.left) (show (Set.range f.left ∩ Set.range g.left).Nonempty from ⟨x, hxf, hxg⟩)
    hc.isLocallyClosed
  let p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := (Foundations.Scheme.ComplexPointExistence.complexOverPointsEquivClosedPoints X.hom).symm ⟨z, hzc⟩
  have hp : p.left (IsLocalRing.closedPoint ℂ) = z :=
    congrArg Subtype.val ((Foundations.Scheme.ComplexPointExistence.complexOverPointsEquivClosedPoints X.hom).apply_symm_apply ⟨z, hzc⟩)
  obtain ⟨a, ha⟩ := (Albanese.Construction.ClosedPoints.pointMap_range_iff Y X f p).mpr (hp.symm ▸ hz.1)
  obtain ⟨b, hb⟩ := (Albanese.Construction.ClosedPoints.pointMap_range_iff Z X g p).mpr (hp.symm ▸ hz.2)
  exact h a b (ha.trans hb.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComplexClosedImageDisjointness
