import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedFunction
import OAI.AlgebraicGeometry.Divisors.LineBundles.IsomorphismDivisorPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization

/-! # Normalized Principal Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedPrincipalCycle.BundleCycles

noncomputable section

/-! The exact finite principal cycle on a general singular support is
the residue-degree-weighted pushforward from its actual smooth normalization
open. Every branch and pole is retained. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.Principal.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [AlgebraicGeometry.IsNoetherian X.left]
    (W : IrreducibleCloseds X.left)

local notation "U" => OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizedOpen X W
local notation "S" => OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint.reducedSupportScheme W

local instance : IsIntegral ((U) : Scheme) := SchemeNormalization.Topology.BundleCycles.schemeSmoothNormalization_integral X W
local instance : Nonempty U := inferInstanceAs (Nonempty ((U) : Scheme))

omit [LocallyOfFiniteType X.hom] in
theorem closedSupport_principalPointPushforward (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    CycleClass.Thom.Point.Constructions.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι W) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S g) = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g := by
  have h : CycleClass.Thom.Point.Constructions.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι W) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S g) =
      Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S g) :=
    IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion (CycleClass.Geometric.GenericPoint.reducedSupportι W) _
  exact h.trans (Finsupp.embDomain_eq_mapDomain
    ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩ (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor S g)).symm

theorem schemeNormalizedPrincipal_pointPushforward (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    CycleClass.Thom.Point.Constructions.pointPushforward (NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap X W).left
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left (NormalizedFunction.BundleCycles.schemeNormalizedFunction X W g)) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g := by
  have ho := CycleClass.Thom.Open.Principal.Constructions.principalDivisor_open_pushforward (SchemeNormalization.AmbientMap.BundleCycles.schemeFullNormalizationOver X W).left U
    (NormalizedFunction.BundleCycles.schemeNormalizationOpen_divisorPoint X W) ((CycleClass.Thom.Normalization.Fields.Constructions.normalizationFieldIso S).hom g)
  have hn := CycleClass.Thom.NormalizationDivisor.Pushforward.Constructions.Local.normalizationPrincipalDivisor_pushforward S (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom) g hg
  have hcomp := CycleClass.Thom.Point.Constructions.pointPushforward_comp (U).ι (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W)
  have hmap := congrArg CycleClass.Thom.Point.Constructions.pointPushforward (NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap_left X W)
  have h₁ := LinearMap.congr_fun (hmap.trans hcomp)
    (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left (NormalizedFunction.BundleCycles.schemeNormalizedFunction X W g))
  have h₂ := congrArg (CycleClass.Thom.Point.Constructions.pointPushforward (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W)) ho
  have h₃ := LinearMap.congr_fun (CycleClass.Thom.Point.Constructions.pointPushforward_comp (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap S) (CycleClass.Geometric.GenericPoint.reducedSupportι W))
    (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (SchemeNormalization.AmbientMap.BundleCycles.schemeFullNormalizationOver X W).left ((CycleClass.Thom.Normalization.Fields.Constructions.normalizationFieldIso S).hom g))
  exact h₁.trans (h₂.trans (h₃.trans ((congrArg (CycleClass.Thom.Point.Constructions.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι W)) hn).trans
    (closedSupport_principalPointPushforward X W g))))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedPrincipalCycle.BundleCycles
