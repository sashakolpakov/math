import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianRegularizationProducts
import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianRegularizationTransport
import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianCutoff

/-! # Quadratic Gaussian Regularization -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticGaussianRegularization.Construction

noncomputable section

/-! Coordinate-independent regularizations for additive quadratic phases. -/

open _root_.MeasureTheory
open scoped BigOperators NNReal

def HasGaussianRegularization
    {F V : Type} [Field F] [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (μ : Measure V) (ψ : AddChar F ℂ) (q : V → F) (Γ : ℂ) : Prop :=
  Nonempty (ComplexGaussianFourier.Construction.GaussianFourierRegularization μ (fun v => ψ (q v)) (fun w => ψ (-q w))
    (fun v w => ψ (q (v + w) - q v - q w)) Γ)

namespace HasGaussianRegularization

theorem smul_measure {F V : Type} [Field F] [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    {μ : Measure V} {ψ : AddChar F ℂ} {q : V → F} {Γ : ℂ}
    (hΓ : HasGaussianRegularization μ ψ q Γ) (c : ℝ≥0) (hc : 0 < c) :
    HasGaussianRegularization (c • μ) ψ q ((c : ℂ) * Γ) :=
  ⟨hΓ.some.smul_measure c hc⟩

theorem transport {F V W : Type} [Field F] [AddCommGroup V] [AddCommGroup W]
    [TopologicalSpace V] [TopologicalSpace W]
    [MeasurableSpace V] [MeasurableSpace W] [BorelSpace V] [BorelSpace W]
    (e : V ≃ₜ+ W) (μ : Measure V) (ψ : AddChar F ℂ) (q : W → F) (Γ : ℂ)
    (hΓ : HasGaussianRegularization (μ.map e) ψ q Γ) :
    HasGaussianRegularization μ ψ (fun x => q (e x)) Γ := by
  have R := hΓ.some.homeomorph e.toHomeomorph rfl
  have heq : (fun v w => ψ (q (e v + e w) - q (e v) - q (e w))) =
      (fun v w => ψ (q (e (v + w)) - q (e v) - q (e w))) := by
    funext v w
    rw [map_add]
  exact ⟨heq ▸ R⟩

theorem finite_product {F V I : Type} [Field F] [AddCommGroup V]
    [TopologicalSpace V] [MeasurableSpace V] [Fintype I]
    (μ : Measure V) [SigmaFinite μ] (ψ : AddChar F ℂ)
    (q : I → V → F) (Γ : I → ℂ) (hΓ : ∀ i, HasGaussianRegularization μ ψ (q i) (Γ i)) :
    HasGaussianRegularization (Measure.pi (fun _ : I => μ)) ψ
      (fun x => ∑ i, q i (x i)) (∏ i, Γ i) := by
  have R := ComplexGaussianFourier.Construction.GaussianFourierRegularization.finite_product (fun _ : I => μ)
    (fun i v => ψ (q i v)) (fun i w => ψ (-q i w))
    (fun i v w => ψ (q i (v + w) - q i v - q i w)) Γ (fun i => (hΓ i).some)
  have hphase : (fun v : I → V => ∏ i, ψ (q i (v i))) = (fun v => ψ (∑ i, q i (v i))) := by
    funext v
    exact (GaussianCutoff.Construction.addChar_sum_product ψ Finset.univ _).symm
  have hdual : (fun v : I → V => ∏ i, ψ (-q i (v i))) = (fun v => ψ (-∑ i, q i (v i))) := by
    funext v
    rw [← GaussianCutoff.Construction.addChar_sum_product, Finset.sum_neg_distrib]
  have hkernel : (fun v w : I → V => ∏ i, ψ (q i (v i + w i) - q i (v i) - q i (w i))) =
      (fun v w => ψ ((∑ i, q i ((v + w) i)) - (∑ i, q i (v i)) - ∑ i, q i (w i))) := by
    funext v w
    rw [← GaussianCutoff.Construction.addChar_sum_product, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rfl
  exact ⟨hphase ▸ hdual ▸ hkernel ▸ R⟩

theorem fourier_pairing_comp
    {F V : Type} [Field F] [AddCommGroup V] [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {μ : Measure V} [SigmaFinite μ] {ψ : AddChar F ℂ} {q : V → F} {Γ : ℂ}
    (hΓ : HasGaussianRegularization μ ψ q Γ)
    (B : V → V → F) (hadd : ∀ v w, q (v + w) = q v + q w + B v w)
    (L : V → V) (hL : Continuous L)
    (f : V → ℂ) (hfc : Continuous f) (hfi : Integrable f μ)
    (hTc : Continuous (fun v => ∫ w, ψ (B v (L w)) * f w ∂μ))
    (hTi : Integrable (fun v => ∫ w, ψ (B v (L w)) * f w ∂μ) μ) :
    (∫ v, ψ (q v) * (∫ w, ψ (B v (L w)) * f w ∂μ) ∂μ) =
      Γ * ∫ w, ψ (-q (L w)) * f w ∂μ := by
  have heq : (fun v w => ψ (q (v + L w) - q v - q (L w))) =
      (fun v w => ψ (B v (L w))) := by
    funext v w
    rw [hadd]
    congr 1
    abel
  have R := hΓ.some.comp_right L hL
  rw [heq] at R
  exact R.pairing f hfc hfi hTc hTi

end HasGaussianRegularization

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticGaussianRegularization.Construction
