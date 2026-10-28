import OAI.AlgebraicGeometry.CycleClass.Thom.RationalRegularNormal
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum

/-! # Rational Complement Vanishing -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.RationalComplementVanishing

noncomputable section

/-! The actual boundary and supported divisor class both vanish on opens
where the regular parameter and the divisor support are absent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum.AlgebraicLineBundle
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.RationalUnitEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RationalBoundary.Constructions.LocalMultiplicity
  RationalBoundary.Constructions.Restriction RationalRegularNormal.Constructions

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  {g : X.carrier.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.carrier g)

theorem rationalGlobalBoundary_restrict_zero_of_parameter_nonzero
    (U : X.carrier.Opens) [Nonempty U]
    (p : Γ(X.carrier, U)) (hp : p ≠ 0) (v : Γ(X.carrier, U)ˣ)
    (m : ℤ) (hm : m ≠ 0)
    (he : g = X.carrier.germToFunctionField U v * (X.carrier.germToFunctionField U p) ^ m)
    (W : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (hWU : W ≤ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)
    (hWp : ∀ y : W, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p ⟨y.val, hWU y.property⟩ ≠ 0) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) W 2
      (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) = 0 := by
  let Q := ModuleCat.of ℚ ℚ
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
  let A := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X D.domain : Set T) W
  let j : TopCat.of W ⟶ TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) :=
    TopCat.ofHom ⟨fun y => ⟨y.val, hWU y.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hj : Set.MapsTo j A (RationalUnitEvaluation.Constructions.referenceLocus X D U) := fun _ hy => hy
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q j (RationalBoundary.Constructions.Restriction.localAmbientMap X U) hj
    (RationalBoundary.Constructions.Restriction.localAmbientMap_mapsTo X D U) 2
  have hv := (ConcreteCategory.congr_hom hc (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D)).symm
  change Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q T (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X D.domain : Set T) W 2
      (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (RationalBoundary.Constructions.Restriction.localAmbientMap X U)
        (RationalBoundary.Constructions.Restriction.localAmbientMap_mapsTo X D U) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary X D)) at hv
  rw [RationalBoundary.Constructions.Restriction.rationalGlobalBoundary_localRestriction,
    RationalBoundary.Constructions.LocalMultiplicity.rationalLocalBoundary_power X D U p hp v m hm he, map_zsmul] at hv
  let hp' := RationalUnitEvaluation.Constructions.referenceParameter_ne_zero X D U p v m he hp hm
  let f := RationalBoundary.Constructions.LocalMultiplicity.lineMap (Y := TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p)
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

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {f : V.carrier.functionField}
  (B : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative V.carrier f) (Z : Geometric.DimensionCycles.DimensionCycleSupport V 1)
  (hO : (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation B.domain : Set V.analyticSpace) ⊆
    (Set.range Z.analyticInclusion)ᶜ)

include hO in
theorem cycleWithUnitComplement_restrict_away
    (W : Opens V.analyticSpace) (hW : (W : Set V.analyticSpace) ⊆ (Set.range Z.analyticInclusion)ᶜ) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation B.domain : Set V.analyticSpace) W 2
      (RationalRegularNormal.Constructions.cycleWithUnitComplement B Z hO) = 0 := by
  let Q := ModuleCat.of ℚ ℚ
  let k := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (W : Set V.analyticSpace)
  let A := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace)
    (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation B.domain : Set V.analyticSpace) W
  have hk : Set.MapsTo k A (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation B.domain : Set V.analyticSpace) := fun _ hx => hx
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q k (𝟙 (TopCat.of V.analyticSpace)) hk hO 2
  have hv := ConcreteCategory.congr_hom hc Z.rationalSupportedCycleClass
  have hz := DivisorClass.Chern.SupportedDivisorSum.relativeCohomologyMap_zero_of_range_subset Q k A
    (Set.range Z.analyticInclusion)ᶜ (fun _ hx => hO (hk hx)) (fun y => hW y.property) 2
  exact hv.trans (by change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k _ 2 _ = 0; rw [hz]; rfl)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.RationalComplementVanishing
