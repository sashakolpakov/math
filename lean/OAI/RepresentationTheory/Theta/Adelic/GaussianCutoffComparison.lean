import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianCutoff
import OAI.RepresentationTheory.Weil.Local.DiagonalQuadratic

/-! # Gaussian Cutoff Comparison -/

namespace OAI.RepresentationTheory.Theta.Adelic.GaussianCutoffComparison

noncomputable section

/-! Stable quadratic cutoffs have the independently computed LocalWeil Fresnel
coefficient. A nonzero compact test integral detects that coefficient. -/

open scoped Classical

open _root_.Matrix _root_.MeasureTheory
open OAI.RepresentationTheory.Weil.Local.DiagonalQuadratic.Construction OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianCutoff.Construction

theorem diagonal_cutoff_coefficient
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
    (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
    (hn : ∃ x : k, ψ x ≠ 1) {n : ℕ} (a : Fin n → kˣ) (Γ : ℂ)
    (hΓ : Weil.UnitarySplitting.GaussianCutoff.Construction.HasGaussianCutoffs (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ) ψ
      (Weil.Local.FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal fun i => (a i).val)) Γ) :
    Γ = Weil.Local.DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a := by
  let : SecondCountableTopology k := Weil.Local.FunctionsMetaplectic.Construction.localField_secondCountable k hnd
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    Weil.Local.NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hnd ψ hu hc hn
  let μ := Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k n ψ
  let : μ.IsAddHaarMeasure := by dsimp [μ, Weil.Local.FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  obtain ⟨f, hf⟩ := Weil.Local.DiagonalQuadratic.Construction.exists_nonarchimedean_quadratic_pairing_ne_zero hnd ψ hu hc μ
    (Matrix.diagonal fun i => (a i).val⁻¹)
  obtain ⟨hfl, hfs⟩ := Weil.UnitarySplitting.UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp f.property
  have hFs := Weil.Local.CompactCharacter.Construction.fourierIntegral_compactSupport_of_locallyConstant
    hnd ψ hn μ hfl hfs
  let q := Weil.Local.FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal fun i => (a i).val)
  let B : Weil.Local.FunctionsMetaplectic.Construction.Position k n → Weil.Local.FunctionsMetaplectic.Construction.Position k n → k := fun x y => ∑ i, (a i).val * x i * y i
  let L : Weil.Local.FunctionsMetaplectic.Construction.Position k n → Weil.Local.FunctionsMetaplectic.Construction.Position k n := fun y i => -y i / (a i).val
  have hqc : Continuous q := by
    change Continuous (fun x : Weil.Local.FunctionsMetaplectic.Construction.Position k n => Weil.Local.FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal fun i => (a i).val) x)
    simp_rw [Weil.Local.RealDiagonalFresnel.Construction.quadratic_diagonal]
    fun_prop
  have hBc : Continuous (fun p : Weil.Local.FunctionsMetaplectic.Construction.Position k n × Weil.Local.FunctionsMetaplectic.Construction.Position k n => B p.1 p.2) := by
    dsimp only [B]
    fun_prop
  have hBs (x y : Weil.Local.FunctionsMetaplectic.Construction.Position k n) : B x y = B y x := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hadd (v x : Weil.Local.FunctionsMetaplectic.Construction.Position k n) : q (v + x) = q v + q x + B v x := by
    simp only [q, Weil.Local.RealDiagonalFresnel.Construction.quadratic_diagonal, Pi.add_apply, B, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
    ring
  have hLc : Continuous L := by dsimp only [L]; fun_prop
  have hBL (x y : Weil.Local.FunctionsMetaplectic.Construction.Position k n) : B x (L y) = -Weil.Local.FunctionsMetaplectic.Construction.dot x y := by
    dsimp only [B, L, Weil.Local.FunctionsMetaplectic.Construction.dot]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hqL (y : Weil.Local.FunctionsMetaplectic.Construction.Position k n) :
      q (L y) = Weil.Local.FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal fun i => (a i).val⁻¹) y := by
    simp only [q, Weil.Local.RealDiagonalFresnel.Construction.quadratic_diagonal, L]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hT : (fun x => ∫ y, ψ (B x (L y)) * f.val y ∂μ) = Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val := by
    funext x
    rw [Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change ψ (B x (L y)) * f.val y = f.val y * ψ (-Weil.Local.FunctionsMetaplectic.Construction.dot x y)
      rw [hBL]
      ring
  have hp := Weil.UnitarySplitting.GaussianCutoff.Construction.gaussianCutoff_fourier_pairing_comp ψ hc hu μ q hqc B hBc hBs hadd Γ hΓ
    L hLc f.val hfl.continuous hfs (by rw [hT]; exact hFs)
  have hTx (x : Weil.Local.FunctionsMetaplectic.Construction.Position k n) :
      (∫ y, ψ (B x (L y)) * f.val y ∂μ) = Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x := congrFun hT x
  simp_rw [hTx] at hp
  have heLeft : (∫ x, ψ (q x) * Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x ∂μ) =
      ∫ x, Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x * ψ (q x) ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => mul_comm _ _
  have heRight : (∫ y, ψ (-q (L y)) * f.val y ∂μ) =
      ∫ y, f.val y * ψ (-Weil.Local.FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal fun i => (a i).val⁻¹) y) ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by dsimp only; rw [hqL]; ring
  rw [heLeft, heRight] at hp
  have hF := Weil.Local.DiagonalQuadratic.Construction.nonarchimedean_diagonal_fresnel_pairing hnd ψ hu hc hn a f
  change (∫ x, Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x * ψ (q x) ∂μ) = _ at hF
  rw [hF] at hp
  exact (mul_right_cancel₀ hf hp).symm

end

end OAI.RepresentationTheory.Theta.Adelic.GaussianCutoffComparison
