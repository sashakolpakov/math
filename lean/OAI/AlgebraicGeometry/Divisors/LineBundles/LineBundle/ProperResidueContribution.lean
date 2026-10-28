import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionGlobalDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ResidueDifference
import OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueCycleFamily

/-! # Proper Residue Contribution -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueContribution.Cycles

noncomputable section

/-! # LineBundleCycles: the actual proper-intersection difference for a rational section and a rational function -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (a g : X.functionFieldˣ)
    (hproper : Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g.val).support)

include hproper in
theorem properSection_function_order_zero (x : X)
    (hx : L.rationalSectionPointDivisorWithCoefficient a x ≠ 0) : X.ord g.val x = 0 := by
  classical
  by_contra hg
  exact Finset.disjoint_left.mp hproper (Finsupp.mem_support_iff.mpr hx) (Finsupp.mem_support_iff.mpr hg)

include hproper in
theorem properSection_section_order_zero (x : X) (hx : X.ord g.val x ≠ 0) :
    L.rationalSectionPointDivisorWithCoefficient a x = 0 := by
  by_contra hs
  exact hx (properSection_function_order_zero L a g hproper x hs)

variable (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

def properLineBundleResidueContribution (x : {x : X // coheight x = 1}) : X →₀ ℚ := by
  classical
  let := hNormal x
  exact if ha : L.rationalSectionPointDivisorWithCoefficient a x = 0 then
    X.ord g.val x • L.restrictedRationalSectionPointCycle a x x.property ha
  else
    -(L.rationalSectionPointDivisorWithCoefficient a x •
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x.val)
        (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x x.property g (properSection_function_order_zero L a g hproper x ha)).val)

theorem properLineBundleResidueContribution_zero_section
    (x : {x : X // coheight x = 1}) (ha : L.rationalSectionPointDivisorWithCoefficient a x = 0) :
    letI := hNormal x
    properLineBundleResidueContribution L a g hproper hNormal x =
      X.ord g.val x • L.restrictedRationalSectionPointCycle a x x.property ha := by
  unfold properLineBundleResidueContribution
  rw [dite_eq_left ha]

theorem properLineBundleResidueContribution_nonzero_section
    (x : {x : X // coheight x = 1}) (ha : L.rationalSectionPointDivisorWithCoefficient a x ≠ 0) :
    letI := hNormal x
    properLineBundleResidueContribution L a g hproper hNormal x =
      -(L.rationalSectionPointDivisorWithCoefficient a x •
        Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x.val)
          (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x x.property g (properSection_function_order_zero L a g hproper x ha)).val) := by
  unfold properLineBundleResidueContribution
  rw [dite_eq_right ha]

theorem properLineBundleResidueContribution_globalFrame
    (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X) (x : {x : X // coheight x = 1}) :
    properLineBundleResidueContribution L a g hproper hNormal x =
      ResidueCycleFamily.BundleCycles.normalResidueContribution X hNormal (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e) g x := by
  let := hNormal x
  by_cases ha : L.rationalSectionPointDivisorWithCoefficient a x = 0
  · rw [properLineBundleResidueContribution_zero_section L a g hproper hNormal x ha]
    exact (RestrictionGlobalDivisor.Cycles.normalResidue_restrictedSection_globalFrame e a x x.property ha g).symm
  · rw [properLineBundleResidueContribution_nonzero_section L a g hproper hNormal x ha]
    have hg := properSection_function_order_zero L a g hproper x ha
    change _ = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x.val)
      (Normal.PointResidue.BundleCycles.normalPointResidueFunction X x x.property (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e) g)
    rw [Normal.ResidueDifference.BundleCycles.normalResidue_principal_swap X x x.property g (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e),
      Normal.RationalRestrictionResidue.BundleCycles.normalResidue_principal_order_zero X x x.property g (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e) hg,
      GlobalDivisor.Cycles.lineBundleGlobal_section_order e a x]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueContribution.Cycles
