import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueContribution
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionOpenCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RestrictionOpenDivisor

/-! # Proper Residue Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueOpen.Cycles

noncomputable section

/-! # LineBundleCycles: each actual proper-intersection contribution commutes with open restriction -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (i : Y ⟶ X) [IsOpenImmersion i] (a g : X.functionFieldˣ)
    (hproper : Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g.val).support)

include hproper in
theorem openProperSection :
    Disjoint ((L.pullback i).rationalSectionPointDivisorWithCoefficient (L.openPullbackSectionCoefficient i a)).support
      (Ord.BundleCycles.principalDivisor Y (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i g).val).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro y ha hg
  have he : (L.pullback i).rationalSectionPointDivisorWithCoefficient (L.openPullbackSectionCoefficient i a) y =
      L.rationalSectionPointDivisorWithCoefficient a (i y) :=
    congrArg (fun D : Y →₀ ℤ => D y) (L.openPullback_section_divisor i a)
  have hga : Y.ord (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i g).val y ≠ 0 := Finsupp.mem_support_iff.mp hg
  have haa : L.rationalSectionPointDivisorWithCoefficient a (i y) ≠ 0 :=
    fun hz => (Finsupp.mem_support_iff.mp ha) (he.trans hz)
  exact hga ((Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits_order i g y).trans (ProperResidueContribution.Cycles.properSection_function_order_zero L a g hproper (i y) haa))

variable (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNormalY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

theorem properLineBundleResidueContribution_open (y : {y : Y // coheight y = 1}) :
    Finsupp.comapDomain i
      (ProperResidueContribution.Cycles.properLineBundleResidueContribution L a g hproper hNormal
        ⟨i y, (coheight_eq_of_isOpenImmersion i).trans y.property⟩) i.isOpenEmbedding.injective.injOn =
      ProperResidueContribution.Cycles.properLineBundleResidueContribution (L.pullback i) (L.openPullbackSectionCoefficient i a)
        (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i g) (openProperSection L i a g hproper) hNormalY y := by
  let := hNormal (i y)
  let := hNormalY y
  let x : {x : X // coheight x = 1} := ⟨i y, (coheight_eq_of_isOpenImmersion i).trans y.property⟩
  let C : (X →₀ ℚ) →+ (Y →₀ ℚ) := Finsupp.comapDomain.addMonoidHom i.isOpenEmbedding.injective
  let b := L.openPullbackSectionCoefficient i a
  let k := Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i g
  let hp := openProperSection L i a g hproper
  have he : (L.pullback i).rationalSectionPointDivisorWithCoefficient b y =
      L.rationalSectionPointDivisorWithCoefficient a (i y) :=
    congrArg (fun D : Y →₀ ℤ => D y) (L.openPullback_section_divisor i a)
  change C (ProperResidueContribution.Cycles.properLineBundleResidueContribution L a g hproper hNormal x) = _
  by_cases ha : L.rationalSectionPointDivisorWithCoefficient a (i y) = 0
  · have ha' := he.trans ha
    have hs := RestrictionOpenCycle.Cycles.restrictedRationalSectionPointCycle_open L i y a x.property y.property ha ha'
    rw [ProperResidueContribution.Cycles.properLineBundleResidueContribution_zero_section L a g hproper hNormal x ha,
      ProperResidueContribution.Cycles.properLineBundleResidueContribution_zero_section (L.pullback i) b k hp hNormalY y ha', map_zsmul]
    exact congrArg₂ (fun n : ℤ => fun z : Y →₀ ℚ => n • z)
      (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits_order i g y).symm hs.symm
  · have ha' : (L.pullback i).rationalSectionPointDivisorWithCoefficient b y ≠ 0 :=
      fun hz => ha (he.symm.trans hz)
    have hg := ProperResidueContribution.Cycles.properSection_function_order_zero L a g hproper (i y) ha
    have hg' := ProperResidueContribution.Cycles.properSection_function_order_zero (L.pullback i) b k hp y ha'
    have hs := Normal.RestrictionOpenDivisor.BundleCycles.normalRationalRestriction_principal_open i y x.property y.property g hg hg'
    rw [ProperResidueContribution.Cycles.properLineBundleResidueContribution_nonzero_section L a g hproper hNormal x ha,
      ProperResidueContribution.Cycles.properLineBundleResidueContribution_nonzero_section (L.pullback i) b k hp hNormalY y ha', map_neg, map_zsmul]
    exact congrArg Neg.neg (congrArg₂ (fun n : ℤ => fun z : Y →₀ ℚ => n • z) he.symm hs)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueOpen.Cycles
