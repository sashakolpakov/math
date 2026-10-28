import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformAtlasFiniteRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.NormalChartProgramPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorization

/-! # Uniform Atlas Pointed Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled

noncomputable section

/-! Pulling back a global modeled atlas program constructs a retained integral chart program at each new order point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem UniformCarrierAtlasProgram.Construction.ModeledUniformCarrierAtlasProgram.exists_chart_on_etale_comparison
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y V W : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    {D : β → X.IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {K : Y.IdealSheafData} {M : W.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) Y g K}
    (A : UniformCarrierAtlasProgram.Construction.ModeledUniformCarrierAtlasProgram 𝒮 schedule f J D P) (q : V ⟶ X) [Etale q]
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V (q ≫ f) (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (q ≫ f) (J.comap q) n) W k M)
    (r : W ⟶ Y) (hc : P.EtaleComparison Q q r)
    (y : V) (hy : y ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (q ≫ f) (J.comap q) n).support) :
    Nonempty (UniformAtlasFiniteRefinement.Construction.ModeledUniformChartProgram 𝒮 schedule (q ≫ f) (J.comap q) (fun l => (D l).comap q) Q y) := by
  have horder : q y ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support := by
    rw [← Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale f J n q, Scheme.IdealSheafData.support_comap] at hy
    exact hy
  obtain ⟨i, p, hp⟩ := A.cover (q y) horder
  obtain ⟨B, hB, hHB, φ, hφ, hcomm, _, hnormal, _, _⟩ :=
    Pointed.ModeledNormalChartPullback.Construction.exists_pointed_integral_modeled_normal_chart_pullback (A.chart i) q y p hp horder
  let : IsDomain B.chart.ring := hB
  let : IsIntegral B.chart.nativeCarrier.subscheme := hHB
  let : IsNoetherianRing B.chart.ring := Algebra.FiniteType.isNoetherianRing ℂ B.chart.ring
  let : IsLocallyNoetherian (Spec B.chart.ring) := inferInstance
  let : IsIntegral (Spec B.chart.ring) := inferInstance
  let : Smooth ((A.chart i).chart.nativeCarrier.subschemeι ≫ ((A.chart i).chart.map ≫ f)) :=
    (A.chart i).chart.nativeCarrier_smooth
  let : Smooth (B.chart.nativeCarrier.subschemeι ≫ (B.chart.map ≫ (q ≫ f))) := B.chart.nativeCarrier_smooth
  let a := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : Etale a := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hφ
  obtain ⟨Z, h, L, R, t, hR⟩ := Q.exists_etale_pullback (Spec B.chart.ring) (B.chart.map ≫ (q ≫ f))
    ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (q ≫ f) (J.comap q) n).comap B.chart.map) B.chart.map rfl rfl
  have hPR := hc.comp P Q q r R B.chart.map t hR
  obtain ⟨u, hu, _⟩ := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_factor P (A.localPrefix i) R
    (A.chart i).chart.map (A.comparisonMap i) (B.chart.map ≫ q) (t ≫ r) (A.comparison i) hPR a hcomm
  obtain ⟨⟨certificate⟩, hC, hd⟩ := (A.certificate i).exists_on_transported_normal_chart q (A.chart i) B
    φ hφ hcomm hnormal (A.coefficientNonzero i) (A.carrierDimension i) R u hu
  exact ⟨{
    chart := B
    domain := hB
    carrierIntegral := hHB
    carrierDimension := hd
    coefficientNonzero := hC
    endpoint := Z
    structureMap := h
    ideal := L
    localPrefix := R
    certificate := certificate
    comparisonMap := t
    comparison := hR }⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled
