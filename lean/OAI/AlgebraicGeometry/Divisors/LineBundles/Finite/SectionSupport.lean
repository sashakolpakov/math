import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.BaseImageClass
import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphEquationSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation

/-! # Section Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionSupport.BundleCycles

noncomputable section

/-! The actual graph equation intersection lies over the original finite-image support intersected with the section zero locus, with the original coordinate bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphEquationSupport.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsNoetherian N.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] (k : S ⟶ N) [IsFinite k.left]
  {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (a : X ⟶ S) [IsOpenImmersion a.left] (j : Y ⟶ N) [IsOpenImmersion j.left]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hUJ : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (s : Γ(Y.left, ⊤)) {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

abbrev finiteBaseSectionImage := CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)

def finiteSectionIntersectionSupport : Set U := BaseImageClass.BundleCycles.finiteParentBaseSupport k U ∩ Set.range (finiteBaseSectionImage j U hUJ s)

omit [IsOpenImmersion a.left] in
omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteSectionGraph_intersection_bound (K : Set (Fin d → ℂ))
    (hb : ∀ x, ParentGraph.BundleCycles.finiteParentGraphBase k a x ∈ U → CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f x ∈ K) :
    Set.range (ParentGraph.BundleCycles.finiteParentGraph k a U f) ∩
      Set.range (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage
        (CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ))
        (CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionZeroImage Y d s)) ⊆ finiteSectionIntersectionSupport k j U hUJ s ×ˢ K := by
  intro y hy
  have hp := ParentGraphProjection.BundleCycles.finiteParentGraph_bound k a U f K hb hy.1
  refine ⟨⟨hp.1, ?_⟩, hp.2⟩
  have hs := (Set.ext_iff.mp (CycleClass.Thom.IntrinsicGraphEquationSupport.Constructions.Intrinsic.graphEquationSupport_range j d U hUJ (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)) y).mp hy.2
  exact (Set.ext_iff.mp (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_range
    (TopCat.prodFst (X := TopCat.of U) (Y := TopCat.of (Fin d → ℂ))) (finiteBaseSectionImage j U hUJ s)) y).mp hs

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionSupport.BundleCycles
