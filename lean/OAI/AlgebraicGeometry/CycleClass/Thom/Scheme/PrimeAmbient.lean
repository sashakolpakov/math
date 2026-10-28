import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeAmbientNormalPair
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportedNormalRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Prime Ambient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeAmbient.Constructions.Class

noncomputable section

/-! The canonical class of any prime divisor restricts to the actual
normalized ambient normal class near each point of its regular locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularDivisorImmersion.Constructions
  SchemeDivisor.Module.Constructions PrimeAmbientNormalPair.Constructions SupportedNormalRestriction.Constructions
  Open.NormalNeighborhoodInverse.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (z : {x : X.left // Order.coheight x = 1})
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)))

theorem ambientPair_mapsTo : Set.MapsTo
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).neighborhood)
    (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).relativeComplement
    (Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ := by
  intro y hy hs
  exact (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).normalCoordinate_mapsTo hy
    ((PrimeAmbientNormalPair.Constructions.primeAmbientPair_zero_iff X z x y).mpr hs)

variable [AlgebraicGeometry.IsNoetherian X.left]

theorem supportedDivisorClass_ambientNormalRestriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).neighborhood)
      (ambientPair_mapsTo X z x) 2 (SchemeDivisor.Module.Constructions.supportedDivisorClass X z) =
    (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).rationalClassFin := by
  let Q := (RegularDivisorImmersion.Constructions.regularPrimeImmersion X z).regularFixedNormalPair x
  let G := RegularSupport.Constructions.regularAmbientOpen X (SchemeDivisor.Purity.Constructions.primeSupport X z)
  let k := SupportedNormalRestriction.Constructions.regularPairAmbientMap X z x Q
  let j := Open.NormalNeighborhoodInverse.Constructions.liftedNormalInverse G Q
  have hk := SupportedNormalRestriction.Constructions.regularPairAmbientMap_mapsTo X z x Q Q.relativeComplement (fun _ hx => hx)
  have hj := Open.NormalNeighborhoodInverse.Constructions.inverse_mapsTo G Q
  have hq := SupportedNormalRestriction.Constructions.supportedDivisorClass_normalRestriction X z x Q Q.relativeComplement (fun _ hx => hx)
  have hr := SchemeDivisor.Module.Constructions.regularDivisorThomClass_restrict X z x Q
    ((RegularDivisorImmersion.Constructions.regularPrimeImmersion X z).regularFixedNormalPair_ambientChart_mdifferentiable x)
  have hv : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k hk 2
      (SchemeDivisor.Module.Constructions.supportedDivisorClass X z) = Q.rationalClassFin := by
    exact hq.trans ((congrArg (fun b => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (𝟙 (TopCat.of Q.neighborhood)) (fun _ hx => hx) 2 b) hr).trans
      (ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ)
        (TopCat.of Q.neighborhood) Q.relativeComplement 2) Q.rationalClassFin))
  have he : j ≫ k = Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).neighborhood := by
    ext y
    rfl
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j k hj hk 2
  have hm := ThomOpenRestriction.Constructions.pairMap_congr he (fun _ hx => hk (hj hx))
    (ambientPair_mapsTo X z x) 2
  have hcomp := ConcreteCategory.congr_hom (hc.trans hm) (SchemeDivisor.Module.Constructions.supportedDivisorClass X z)
  have hn := Open.NormalNeighborhoodInverse.Constructions.inverse_normalClass G Q
  exact hcomp.symm.trans ((congrArg
    (fun b => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) j hj 2 b) hv).trans hn)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeAmbient.Constructions.Class
