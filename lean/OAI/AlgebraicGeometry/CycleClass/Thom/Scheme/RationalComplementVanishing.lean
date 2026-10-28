import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalRegularNormal
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum

/-! # Rational Complement Vanishing -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalComplementVanishing

noncomputable section

/-! The actual boundary and supported divisor class both vanish on opens
where the regular parameter and the divisor support are absent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module.Constructions
  RationalUnitEvaluation.Constructions RationalBoundary.Constructions.LocalMultiplicity
  RationalBoundary.Constructions.Restriction RationalRegularNormal.Constructions

section Boundary
variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left]
  {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g)

theorem rationalGlobalBoundary_restrict_zero_of_parameter_nonzero
    (U : X.left.Opens) [Nonempty U]
    (p : Γ(X.left, U)) (hp : p ≠ 0) (v : Γ(X.left, U)ˣ)
    (m : ℤ) (hm : m ≠ 0)
    (he : g = X.left.germToFunctionField U v * (X.left.germToFunctionField U p) ^ m)
    (W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hWU : W ≤ SectionEvaluation.Constructions.analyticOpen X U)
    (hWp : ∀ y : W, SectionEvaluation.Constructions.sectionEvaluationOn X U p ⟨y.val, hWU y.property⟩ ≠ 0) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) W 2
      (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) = 0 := by
  let Q := ModuleCat.of ℚ ℚ
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  let A := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (SectionEvaluation.Constructions.analyticOpen X D.domain : Set T) W
  let j : TopCat.of W ⟶ TopCat.of (SectionEvaluation.Constructions.analyticOpen X U) :=
    TopCat.ofHom ⟨fun y => ⟨y.val, hWU y.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hj : Set.MapsTo j A (RationalUnitEvaluation.Constructions.referenceLocus X D U) := fun _ hy => hy
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q j (RationalBoundary.Constructions.Restriction.localAmbientMap X U) hj
    (RationalBoundary.Constructions.Restriction.localAmbientMap_mapsTo X D U) 2
  have hv := (ConcreteCategory.congr_hom hc (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D)).symm
  change Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q T (SectionEvaluation.Constructions.analyticOpen X D.domain : Set T) W 2
      (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (RationalBoundary.Constructions.Restriction.localAmbientMap X U)
        (RationalBoundary.Constructions.Restriction.localAmbientMap_mapsTo X D U) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D)) at hv
  rw [RationalBoundary.Constructions.Restriction.rationalGlobalBoundary_localRestriction,
    RationalBoundary.Constructions.LocalMultiplicity.rationalLocalBoundary_power X D U p hp v m hm he, map_zsmul] at hv
  let hp' := RationalUnitEvaluation.Constructions.referenceParameter_ne_zero X D U p v m he hp hm
  let f := RationalBoundary.Constructions.LocalMultiplicity.lineMap (Y := TopCat.of (SectionEvaluation.Constructions.analyticOpen X U)) (SectionEvaluation.Constructions.sectionEvaluationOn X U p)
  have hf := RationalBoundary.Constructions.LocalMultiplicity.parameterMap_mapsTo X D U p hp'
  have ht := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q j f hj hf 2
  have hall : ∀ y, (j ≫ f) y ∈ PrincipalBoundary.Constructions.puncturedComplexLine := by
    intro y hz
    exact hWp y (congrFun (Set.mem_singleton_iff.mp hz) 0)
  have hz := DivisorClass.Chern.SupportedDivisorSum.relativeCohomologyMap_zero_of_range_subset Q (j ≫ f) A PrincipalBoundary.Constructions.puncturedComplexLine
    (hf.comp hj) hall 2
  have hclass := ConcreteCategory.congr_hom ht (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)
  rw [hz] at hclass
  have hzero : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2
      (RationalBoundary.Constructions.LocalMultiplicity.parameterSupportedClass X D U p hp') = 0 := hclass
  exact hv.trans (by rw [hzero, smul_zero])

end Boundary

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (z : {x : X.left // Order.coheight x = 1}) {f : X.left.functionField}
  (B : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left f)
  (hO : (SectionEvaluation.Constructions.analyticOpen X B.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆
    (Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ)

include hO in
theorem cycleWithUnitComplement_restrict_away
    (W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hW : (W : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ (Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (SectionEvaluation.Constructions.analyticOpen X B.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) W 2
      (RationalRegularNormal.Constructions.cycleWithUnitComplement X z B hO) = 0 := by
  let Q := ModuleCat.of ℚ ℚ
  let k := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (W : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  let A := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (SectionEvaluation.Constructions.analyticOpen X B.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) W
  have hk : Set.MapsTo k A (SectionEvaluation.Constructions.analyticOpen X B.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := fun _ hx => hx
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q k (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hk hO 2
  have hv := ConcreteCategory.congr_hom hc (SchemeDivisor.Module.Constructions.supportedDivisorClass X z)
  have hz := DivisorClass.Chern.SupportedDivisorSum.relativeCohomologyMap_zero_of_range_subset Q k A
    (Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ (fun _ hx => hO (hk hx)) (fun y => hW y.property) 2
  exact hv.trans (by change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k _ 2 _ = 0; rw [hz]; rfl)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RationalComplementVanishing
