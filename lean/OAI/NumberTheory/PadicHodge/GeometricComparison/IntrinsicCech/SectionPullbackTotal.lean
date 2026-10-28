import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PullbackNormalization
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SectionComplexPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionsTotal

/-! # Section Pullback Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionPullbackTotal.IntrinsicCechSectionPullbackTotal

noncomputable section

/-! The actual native section-total comparison commutes with geometric pullback and an actual cover refinement. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

local instance : HasCoproducts.{0} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := Instances.IntrinsicCechInstances.hasCoproducts R X.left
local instance : HasCoproducts.{0} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) := Instances.IntrinsicCechInstances.hasCoproducts R Y.left
local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).Additive where
  map_add := rfl
local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)).Additive where
  map_add := rfl

def cochainMap {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℕ}
    {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ}
    (b : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    SectionsTotal.IntrinsicCechSectionsTotal.integerTotal R Y.left U K ⟶ SectionsTotal.IntrinsicCechSectionsTotal.integerTotal R X.left V L :=
  TotalSection.TotalSectionPullbackNaturality.cochainMap (DeRham.Int.inverseImage f)
    (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)) (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left))
    (Intrinsic.SectionCochainAdjoint.IntrinsicSectionPullback.map f) (PullbackNormalization.IntrinsicCechPullback.bicomplexMap f U V r hr b)

theorem comparison_square {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℕ}
    {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ}
    (b : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    cochainMap f U V r hr b ≫ (SectionsTotal.IntrinsicCechSectionsTotal.iso R X.left V L).hom =
      (SectionsTotal.IntrinsicCechSectionsTotal.iso R Y.left U K).hom ≫
        Intrinsic.SectionComplexPullback.IntrinsicSectionComplexPullback.map f (PullbackTotal.IntrinsicCechPullback.integerMap f U V r hr b) := by
  have h := TotalSection.TotalSectionPullbackNaturality.comparison_square (DeRham.Int.inverseImage f)
    (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)) (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left))
    (Intrinsic.SectionCochainAdjoint.IntrinsicSectionPullback.map f) (PullbackNormalization.IntrinsicCechPullback.bicomplexMap f U V r hr b)
  exact h.trans (congrArg (fun k => (SectionsTotal.IntrinsicCechSectionsTotal.iso R Y.left U K).hom ≫
    Intrinsic.SectionComplexPullback.IntrinsicSectionComplexPullback.map f k) (PullbackNormalization.IntrinsicCechPullback.integerMap_eq f U V r hr b).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionPullbackTotal.IntrinsicCechSectionPullbackTotal
