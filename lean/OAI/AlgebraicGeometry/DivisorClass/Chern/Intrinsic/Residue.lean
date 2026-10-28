import OAI.AlgebraicGeometry.DivisorClass.Chern.NormalCoordinateResidue
import OAI.AlgebraicGeometry.DivisorClass.Chern.LocalEquations
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding

/-! # Residue -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.Residue

noncomputable section

/-!
# ChernClass: the actual Chern residue in a normal pair on the native scheme

The pair lives in the whole native analytic scheme. Pullback through the
actual algebraic open and its original section equation gives the exact
algebraic multiplicity in that same pair, retaining the primitive sign.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding.Constructions OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen

variable (U : X.carrier.Opens) (p : Γ(X.carrier, U)) (x : Line.Bundles.AlgebraicLineBundle.analyticOpen X U)
  (hxp : Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p x = 0) {d : ℕ}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) ℂ
    (fun z : {y : Line.Bundles.AlgebraicLineBundle.analyticOpen X U // Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y = 0} => z.val.val) ⟨x, hxp⟩)

/-- The actual inclusion into the algebraic open containing this native normal pair. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.nativePairToAlgebraicOpen (hPU : P.neighborhood ⊆ (Line.Bundles.AlgebraicLineBundle.analyticOpen X U : Set T)) :
    TopCat.of P.neighborhood ⟶ TopCat.of (Line.Bundles.AlgebraicLineBundle.analyticOpen X U) :=
  TopCat.ofHom ⟨fun y => ⟨y.val, hPU y.property⟩, by fun_prop⟩

/-- On a native scheme normal pair whose coordinate is the actual regular
parameter, the original relative Chern class has its actual divisor exponent. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_native_parameter [Nonempty U]
    (hPU : P.neighborhood ⊆ (Line.Bundles.AlgebraicLineBundle.analyticOpen X U : Set T))
    (i : X.carrier) (hi : U ≤ L.trivializingOpen i) (hp : p ≠ 0)
    (v : Γ(X.carrier, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : (L.rationalSectionCoordinate i : X.carrier.functionField) =
      X.carrier.germToFunctionField U v * (X.carrier.germToFunctionField U p) ^ m)
    (hcoord : ∀ y : P.neighborhood, P.normalCoordinate y =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p ⟨y.val, hPU y.property⟩) :
    ∃ hA : L.analyticReferenceLocus P.openNeighborhood ⊆ P.relativeComplement,
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) P.openNeighborhood 2
        L.rationalSectionChernRelativeClass =
      m • (NormalWinding.normalWindingCoefficient • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (𝟙 (TopCat.of P.neighborhood)) hA 2 (HodgeConjecture.DegreeTwo.NormalMultiplicity.Constructions.normalChartClass P)) := by
  let A := L.analyticReferenceLocus P.openNeighborhood
  let f := Line.Bundles.AlgebraicLineBundle.nativePairToAlgebraicOpen U p x hxp P hPU
  let hf : Set.MapsTo f A (L.referenceLocus U) := fun _ hy => hy
  have hA : A ⊆ P.relativeComplement := by
    intro y hy hsupport
    obtain ⟨w, hw⟩ := hsupport
    have hn := HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation.referenceParameter_ne_zero L i U hi p hp v m hm he
      (show L.referenceLocus U from ⟨f y, hy⟩)
    apply hn
    have heq : f y = w.val := Subtype.ext hw.symm
    change Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p (f y) = 0
    rw [heq]
    exact w.property
  refine ⟨hA, ?_⟩
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) f
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (Line.Bundles.AlgebraicLineBundle.analyticOpen X U : Set T)) hf
    (A := A) (B := L.referenceLocus U) (C := (O : Set T)) (fun _ hy => hy) 2
  change CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2 ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf 2 =
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) P.openNeighborhood 2 at hc
  have hv := (ConcreteCategory.congr_hom hc L.rationalSectionChernRelativeClass).symm
  change CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) P.openNeighborhood 2
      L.rationalSectionChernRelativeClass =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf 2
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) (Line.Bundles.AlgebraicLineBundle.analyticOpen X U) 2
        L.rationalSectionChernRelativeClass) at hv
  rw [L.rationalSectionChernRelativeClass_algebraic i U hi,
    HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation.rationalSectionLocalSupportedClass_power L i U hi p hp v m hm he, map_zsmul,
    Supported.Winding.supportedWindingClass_pullback] at hv
  refine hv.trans (congrArg (fun a => m • a) ?_)
  apply NormalCoordinateResidue.normalCoordinate_supportedWinding_on_subset P A hA
  intro y
  exact (hcoord y.val).symm

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.Residue
