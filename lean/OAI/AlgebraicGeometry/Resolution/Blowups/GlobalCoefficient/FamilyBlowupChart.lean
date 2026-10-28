import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.IdealReesComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ChartTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BoundaryTransform

/-! # Family Blowup Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient

noncomputable section

/-! Construct retained coefficient-family data on actual global blowup comparison charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

def FamilyCharts.Construction.GlobalCoefficientFamilyChart.blowupChart
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData} {C : H.subscheme.IdealSheafData} {b : ℕ}
    (T : FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b) [IsNoetherianRing T.ring] [Algebra ℚ T.ring]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hHI : H ≤ I) (hp : J ≤ I ^ b)
    (hC : C ≤ (I.comap H.subschemeι) ^ b.factorial)
    (A : Ideal T.ring) (hA : I.comap T.map = Affine.QuotientKernel.Construction.affineQuotientKernel A)
    (hn : T.normal ∈ A) (a : A) (ha : T.derivative a.val = 0)
    (j : Spec (.of (Blowup.Charts.Construction.blowupChart A a)) ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI) [Etale j]
    (hover : j ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI =
      Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants A a)) ≫ T.map) :
    FamilyCharts.Construction.GlobalCoefficientFamilyChart (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1)
      (Transform.Construction.globalRetainedCoefficientTransform I H C hI b) b := by
  let : Algebra ℤ (Blowup.Charts.Construction.blowupChart A a) := Ring.toIntAlgebra _
  let z : A := ⟨T.normal, hn⟩
  let L := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
  let p := T.family
  have hpA : Ideal.span (Set.range p) ≤ A ^ b := by
    have h := Scheme.IdealSheafData.comap_mono T.map hp
    change J.comap T.map ≤ (I ^ b).comap T.map at h
    rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, T.familyIdeal, hA, ← Affine.QuotientKernel.Construction.affineQuotientKernel_pow] at h
    exact (Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff _ _).mp h
  have hL : L.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio A a z}) := by
    have h := GlobalControlled.IdealReesComparison.Construction.globalBlowupControlledIdeal_comap_rees_comparison I H hI 1
      (by simpa only [pow_one] using hHI) T.ring T.map A (Ideal.span {T.normal}) hA T.hypersurface a j hover
    exact h.trans (congrArg Affine.QuotientKernel.Construction.affineQuotientKernel (Coordinate.BoundaryTransform.Construction.blowup_principal_coordinate_controlledTransform A a z))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio A a z})))
  have hker : L.subschemeι.ker ≤ (q ≫ j).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    apply (ControlledIdealKernel.Construction.idealSheaf_le_ker_iff_comap_eq_bot L (q ≫ j)).mpr
    rw [Scheme.IdealSheafData.comap_comp, hL]
    exact (ControlledIdealKernel.Construction.idealSheaf_le_ker_iff_comap_eq_bot _ q).mp le_rfl
  let l := IsClosedImmersion.lift L.subschemeι (q ≫ j) hker
  have hl : l ≫ L.subschemeι = q ≫ j := IsClosedImmersion.lift_fac _ _ _
  refine {
    ring := .of (Blowup.Charts.Construction.blowupChart A a)
    algebra := inferInstance
    map := j
    etale := inferInstance
    ground := ?_
    normal := ExceptionalIdeal.Construction.blowupChartRatio A a z
    hypersurface := hL
    derivative := Relative.DifferentialBlowup.Construction.blowupRelativeChartDerivation ℂ A a T.derivative
    derivative_normal := ?_
    familyIndex := T.familyIndex
    family := ControlledGeneratorFamily.Construction.blowupChartTransformFamily A p a b hpA
    familyIdeal := ?_
    coefficientMap := l
    coefficient_over := hl
    coefficientIdeal := (T.coefficientIdeal.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap A a z)).colon
      (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio A a z})
        (Blowup.Charts.Construction.blowupChartConstants A a a.val)) ^ b.factorial})
    coefficient_eq := ?_
    lower := ?_ }
  · rw [← Category.assoc, hover, Category.assoc, T.ground, ← Spec.map_comp]
    rfl
  · exact Coordinate.BlowupTransform.Construction.blowupChartDerivation_coordinate A a z (T.derivative.restrictScalars ℤ) ha T.derivative_normal
  · have h := GlobalControlled.IdealReesComparison.Construction.globalBlowupControlledIdeal_comap_rees_comparison I J hI b hp T.ring T.map
      A (Ideal.span (Set.range p)) hA T.familyIdeal a j hover
    rw [ControlledGeneratorFamily.Construction.blowupControlledTransform_eq_span_family A p a b hpA] at h
    exact h
  · exact ChartTransform.Construction.globalRetainedCoefficientTransform_comap_hypersurface_chart T I hI hC A hA hn a ha j hover l hl
  · change WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal (ChartDerivation.Construction.blowupChartDerivation A a (T.derivative.restrictScalars ℤ))
      (ExceptionalIdeal.Construction.blowupChartRatio A a z) (ControlledGeneratorFamily.Construction.blowupChartTransformFamily A p a b hpA) b ≤ _
    rw [← WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal_blowup_colon A a z (T.derivative.restrictScalars ℤ)
      ha T.derivative_normal p b hpA]
    exact Submodule.colon_mono (Ideal.map_mono T.lower) le_rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient
