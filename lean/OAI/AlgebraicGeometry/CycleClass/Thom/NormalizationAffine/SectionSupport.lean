import OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph
import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphEquationSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation

/-! # Section Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions

noncomputable section

/-! The actual graph intersection for a base regular section lies over the
original parent cycle intersected with that section's zero support, with
the original compact coordinate bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenGraph.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphEquationSupport.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V D.val) [IsOpenImmersion a.left]
  (j : Y ⟶ V.toOver) [IsOpenImmersion j.left]
  (U : Opens V.analyticSpace) (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (s : Γ(Y.left, ⊤)) {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

def parentBaseSupport : Set U := (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion

abbrev baseSectionImage := ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)

def sectionIntersectionSupport : Set U := parentBaseSupport D U ∩ Set.range (baseSectionImage j U hUJ s)

omit [IsOpenImmersion a.left] in
theorem sectionGraph_intersection_bound (K : Set (Fin d → ℂ))
    (hb : ∀ x, Normalization.GenericFibers.Constructions.Open.openBase D a x ∈ U → Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f x ∈ K) :
    Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph D a U f) ∩
      Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage
        (Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ))
        (Affine.GraphSectionEquation.Constructions.graphSectionZeroImage Y d s)) ⊆ sectionIntersectionSupport D j U hUJ s ×ˢ K := by
  intro y hy
  have hp := Normalization.OpenGraph.Constructions.Class.normalizationOpenGraph_bound D a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) K hb hy.1
  refine ⟨⟨hp.1, ?_⟩, hp.2⟩
  have hs := (Set.ext_iff.mp (IntrinsicGraphEquationSupport.Constructions.Intrinsic.graphEquationSupport_range j d U hUJ (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)) y).mp hy.2
  exact (Set.ext_iff.mp (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_range
    (TopCat.prodFst (X := TopCat.of U) (Y := TopCat.of (Fin d → ℂ))) (baseSectionImage j U hUJ s)) y).mp hs

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions
