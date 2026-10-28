import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.FamilyCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HypersurfaceNormalCover

/-! # Global Coefficient Family Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Initial intrinsic coefficient ideals possess actual fixed-family charts along the entire smooth carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart.ofNativeNormal
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (b : ℕ)
    (U : X.affineOpens) (z : Γ(X, U)) (hHz : H.ideal U = Ideal.span {z}) :
    letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    ∀ (D : Derivation ℂ Γ(X, U) Γ(X, U)), D z = 1 →
      GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι) b := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  intro D hD
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {z})))
  have hHmap : H.comap U.2.fromSpec = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z}) := by
    rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, hHz]
  have hker : H.subschemeι.ker ≤ (i ≫ U.2.fromSpec).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    apply (ControlledIdealKernel.Construction.idealSheaf_le_ker_iff_comap_eq_bot H (i ≫ U.2.fromSpec)).mpr
    rw [Scheme.IdealSheafData.comap_comp, hHmap]
    exact (ControlledIdealKernel.Construction.idealSheaf_le_ker_iff_comap_eq_bot _ i).mp le_rfl
  let l := IsClosedImmersion.lift H.subschemeι (i ≫ U.2.fromSpec) hker
  have hl : l ≫ H.subschemeι = i ≫ U.2.fromSpec := IsClosedImmersion.lift_fac _ _ _
  let p : J.ideal U → Γ(X, U) := Subtype.val
  have hp : Ideal.span (Set.range p) = J.ideal U := by
    change Ideal.span (Set.range (Subtype.val : J.ideal U → Γ(X, U))) = J.ideal U
    rw [Subtype.range_val, Ideal.span_eq]
  refine {
    ring := Γ(X, U)
    algebra := inferInstance
    map := U.2.fromSpec
    etale := inferInstance
    ground := (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U).symm
    normal := z
    hypersurface := hHmap
    derivative := D
    derivative_normal := hD
    familyIndex := J.ideal U
    family := p
    familyIdeal := ?_
    coefficientMap := l
    coefficient_over := hl
    coefficientIdeal := Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal ℂ z (J.ideal U) b
    coefficient_eq := ?_
    lower := ?_ }
  · rw [hp]
    exact Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel J U
  · exact GlobalCoefficient.AffineCharts.Construction.smoothCoefficientIdealSheaf_comap_hypersurface_chart f J b H.subschemeι U.2.fromSpec
      (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U).symm (J.ideal U) z
      (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel J U) l hl
  · have h := Relative.CoefficientFamilyInterval.Construction.weightedCoordinateDerivativeFamilyIdeal_le_relative ℂ D z p b
    rwa [hp] at h

theorem GlobalCoefficientFamilyCharts.Construction.exists_initial_global_coefficient_family_charts
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (hH : H ≠ ⊥)
    [Smooth (H.subschemeι ≫ f)] (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (b : ℕ)
    (x : X) (hx : x ∈ H.support) :
    ∃ T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι) b,
      ∃ p : PrimeSpectrum T.ring, T.map p = x := by
  obtain ⟨U, hxU, hcase⟩ := Global.HypersurfaceNormalCover.Construction.exists_global_hypersurface_normal_neighborhood f H H hH hlocal le_rfl x
  rcases hcase with hunit | hframe
  · have hm := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := H) hxU).mp hx
    rw [hunit] at hm
    change x ∈ X.zeroLocus (Set.univ : Set Γ(X, U)) at hm
    rw [Scheme.zeroLocus_univ] at hm
    exact (hm hxU).elim
  · let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    obtain ⟨ι, hdec, g, D, hD, _, j, hnormal⟩ := hframe
    have hd : D j (g j).val = 1 := by simpa only [ite_true] using hD j j
    let T := GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart.ofNativeNormal f J H b U (g j).val hnormal (D j) hd
    let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    have hxrange : x ∈ U.2.fromSpec.opensRange := by rw [U.2.opensRange_fromSpec]; exact hxU
    obtain ⟨p, hp⟩ := hxrange
    exact ⟨T, p, hp⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
