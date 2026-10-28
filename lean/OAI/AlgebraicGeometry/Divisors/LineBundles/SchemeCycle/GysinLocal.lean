import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleGysin
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.ParameterClass

/-! # Gysin Local -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.GysinLocal.BundleCycles

noncomputable section

/-! Near every regular source-cycle point, the genuine supported Gysin class restricts to the local Gysin map of its actual normal equation in arbitrary codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
  CycleClass.Thom.Normal.GysinRestriction.Constructions CycleClass.Thom.Normal.GysinLocalIso.Constructions
  CycleClass.Thom.Normal.Product.Constructions.Class

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left]
  (Z : IrreducibleCloseds X.left)
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (q : ℕ) (hq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel (Fin p → ℂ)
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x))
  (hP : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' P.neighborhood ⊆ (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x).neighborhood)

abbrev schemeCycleGysinParameter := ParameterClass.BundleCycles.schemeSupportParameter X Z q hq x
  (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding) hP

theorem schemeCycleGysinParameter_zero (y : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding) :
    schemeCycleGysinParameter i Z p hp q hq x P hP y = 0 ↔
      (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion y.val ∉ Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z :=
  (ParameterClass.BundleCycles.schemeSupportParameter_zero_iff X Z q hq x _ hP y).trans (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImage_mem_iff i Z y.val).symm

variable [AlgebraicGeometry.IsNoetherian X.left]

theorem schemeCycleGysinSourceRestriction_normal :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      (CycleClass.Thom.Normal.GysinRestriction.Constructions.sourceMapsTo (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z)
        (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x) P (schemeCycleGysinParameter i Z p hp q hq x P hP)
        (schemeCycleGysinParameter_zero i Z p hp q hq x P hP)) (2 * q)
      ((AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleSourceComplement i Z) (2 * q)).inv
        (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z q hq)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (schemeCycleGysinParameter i Z p hp q hq x P hP)
      (A := schemeCycleGysinParameter i Z p hp q hq x P hP ⁻¹' {0}ᶜ) (B := {0}ᶜ) (fun _ hy => hy) (2 * q)
      (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q) := by
  have hc := CycleClass.Thom.Normal.Product.Constructions.Class.relativeCohomologyMap_targetCast
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleSourceComplement i Z).symm
    (ParameterClass.BundleCycles.schemeSupportParameter_mapsTo X Z q hq x _ hP)
    (CycleClass.Thom.Normal.GysinRestriction.Constructions.sourceMapsTo (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z)
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x) P (schemeCycleGysinParameter i Z p hp q hq x P hP)
      (schemeCycleGysinParameter_zero i Z p hp q hq x P hP)) (2 * q) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z q hq)
  exact hc.trans (ParameterClass.BundleCycles.schemeSupportedCycleClass_parameter X Z q hq x _ hP)

variable
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)

theorem schemeClosedCycleGysinClass_restriction :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) P.openNeighborhood (2 * (p + q))
      (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleGysinClass i Z p hp q hq a ha) =
    (CycleClass.Thom.Normal.GysinLocalIso.Constructions.localGysinIso (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x) P
      (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImage_supported i Z p hp) (schemeCycleGysinParameter i Z p hp q hq x P hP)
      (schemeCycleGysinParameter_zero i Z p hp q hq x P hP) a ha).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (schemeCycleGysinParameter i Z p hp q hq x P hP)
        (A := schemeCycleGysinParameter i Z p hp q hq x P hP ⁻¹' {0}ᶜ) (B := {0}ᶜ) (fun _ hy => hy) (2 * q)
        (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q)) := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Thom.Normal.GysinRestriction.Constructions.globalGysinIso_restriction (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z)
      (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImage_supported i Z p hp) a ha (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x) P
      (schemeCycleGysinParameter i Z p hp q hq x P hP) (schemeCycleGysinParameter_zero i Z p hp q hq x P hP))
    ((AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleSourceComplement i Z) (2 * q)).inv
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z q hq))
  exact h.symm.trans (congrArg
    (fun b => (CycleClass.Thom.Normal.GysinLocalIso.Constructions.localGysinIso (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x) P
      (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImage_supported i Z p hp) (schemeCycleGysinParameter i Z p hp q hq x P hP)
      (schemeCycleGysinParameter_zero i Z p hp q hq x P hP) a ha).hom b)
    (schemeCycleGysinSourceRestriction_normal i Z p hp q hq x P hP))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.GysinLocal.BundleCycles
