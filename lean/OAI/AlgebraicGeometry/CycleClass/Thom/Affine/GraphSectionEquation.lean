import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation
import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo

/-! # Graph Section Equation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions

noncomputable section

/-! An actual base regular section supplies all equation and unit-domain
data on the actual polynomial graph ambient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine Y.left] (d : ℕ) (s : Γ(Y.left, ⊤))

abbrev graphSectionEquation := IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection Y d ≫ GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y s

abbrev graphSectionZeroImage := ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection Y d) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)

theorem graphSectionZeroImage_openComplement : IsOpen (Set.range (graphSectionZeroImage Y d s))ᶜ :=
  ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection Y d) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s)

theorem graphSectionEquation_mapsTo : Set.MapsTo (graphSectionEquation Y d s)
    (Set.range (graphSectionZeroImage Y d s))ᶜ PrincipalBoundary.Constructions.puncturedComplexLine :=
  fun _ hx => GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo Y s (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection Y d) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) hx)

variable {Y} {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [IsAffine X.left]
  (g : X ⟶ Y) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

local instance : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩

variable (hs : X.left.germToFunctionField ⊤ (g.left.appTop s) ≠ 0)

omit [IsIntegral X.left] in
theorem graphSection_nonzero_pullback (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SchemeGraph.Constructions.globalGraphSchemeMap g f) x ∉ Set.range (graphSectionZeroImage Y d s)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x ∉ Set.range (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) := by
  have h := ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection Y d) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) hx
  rwa [IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection_graph] at h

theorem graphSection_unitDomain :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range (graphSectionZeroImage Y d s))ᶜ ⊆
      (Scheme.SectionEvaluation.Constructions.analyticOpen X (GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left (g.left.appTop s) hs).domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :=
  fun _ hx => GlobalSectionUnitEvaluation.Constructions.SchemeEquation.pullback_nonzero_mem_unitDomain s g hs (graphSection_nonzero_pullback d s g f _ hx)

theorem graphSection_unitEvaluation
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range (graphSectionZeroImage Y d s))ᶜ) :
    graphSectionEquation Y d s (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SchemeGraph.Constructions.globalGraphSchemeMap g f) x.val) 0 =
      Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X (GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left (g.left.appTop s) hs).domain
        (GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left (g.left.appTop s) hs).unit.val
        ⟨x.val, graphSection_unitDomain d s g f hs x.property⟩ := by
  change GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y s (IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection Y d (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SchemeGraph.Constructions.globalGraphSchemeMap g f) x.val)) 0 = _
  rw [IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection_graph]
  exact GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_pullback_unit s g hs ⟨x.val, graphSection_nonzero_pullback d s g f x.val x.property⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions
