import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueFamily
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportPointCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportGenericPoint

/-! # Proper Residue Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueSupport.Cycles

noncomputable section

/-! # LineBundleCycles: actual proper-intersection contributions vanish on an open missing their prime support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X Y : Scheme.{0}} (i : Y ⟶ X) [IsOpenImmersion i]

theorem pointSupport_off_open (x : X) (hx : x ∉ Set.range i) (y : Y) :
    i y ∉ (irreducibleSetEquivPoints.symm x : Set X) := by
  intro hy
  have hn := (Open.SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff i (irreducibleSetEquivPoints.symm x)).mpr ⟨y, hy⟩
  have h := (Open.SupportGenericPoint.BundleCycles.openSupportPullback_nonempty_generic i (irreducibleSetEquivPoints.symm x)).mp hn
  rw [irreducibleSetEquivPoints.apply_symm_apply] at h
  exact hx h

theorem pointSupportCycle_open_off_image (x : X) (hx : x ∉ Set.range i)
    (z : CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x) →₀ ℚ) :
    Finsupp.comapDomain i (Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) z)
      i.isOpenEmbedding.injective.injOn = 0 := by
  ext y
  apply Finsupp.mapDomain_of_notMem_range
  rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact pointSupport_off_open i x hx y

variable [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (a g : X.functionFieldˣ)
    (hproper : Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g.val).support)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

theorem properLineBundleResidueContribution_open_off_image (x : {x : X // coheight x = 1})
    (hx : x.val ∉ Set.range i) :
    Finsupp.comapDomain i (ProperResidueContribution.Cycles.properLineBundleResidueContribution L a g hproper hNormal x)
      i.isOpenEmbedding.injective.injOn = 0 := by
  let := hNormal x
  let C : (X →₀ ℚ) →+ (Y →₀ ℚ) := Finsupp.comapDomain.addMonoidHom i.isOpenEmbedding.injective
  change C _ = 0
  by_cases ha : L.rationalSectionPointDivisorWithCoefficient a x = 0
  · have hz : C (L.restrictedRationalSectionPointCycle a x x.property ha) = 0 :=
      pointSupportCycle_open_off_image i x hx _
    rw [ProperResidueContribution.Cycles.properLineBundleResidueContribution_zero_section L a g hproper hNormal x ha, map_zsmul, hz, smul_zero]
  · have hz : C (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x.val)
        (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x x.property g (ProperResidueContribution.Cycles.properSection_function_order_zero L a g hproper x ha)).val) = 0 := by
      ext y
      exact Open.PrincipalRestriction.BundleCycles.schemePrincipalPointDivisor_off_support _ _ (i y) (pointSupport_off_open i x hx y)
    rw [ProperResidueContribution.Cycles.properLineBundleResidueContribution_nonzero_section L a g hproper hNormal x ha,
      map_neg, map_zsmul, hz, smul_zero, neg_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueSupport.Cycles
