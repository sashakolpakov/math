import OAI.Analysis.PDE.Weak.Elliptic.Localization

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure X)

def HasWeakDirectionalDerivativeOn (Ω : Set X) (v : X) (u g : X → E) : Prop :=
  ∀ φ : X → E, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ x, inner ℝ (g x) (φ x) ∂μ) = -(∫ x, inner ℝ (u x) (fderiv ℝ φ x v) ∂μ)

omit [BorelSpace X] [SecondCountableTopology X] in
theorem HasWeakDirectionalDerivativeOn.congr_on
    {Ω : Set X} {v : X} {u g u' g' : X → E}
    (hg : HasWeakDirectionalDerivativeOn μ Ω v u g)
    (hu : ∀ᵐ x ∂μ, x ∈ Ω → u x = u' x)
    (hh : ∀ᵐ x ∂μ, x ∈ Ω → g x = g' x) :
    HasWeakDirectionalDerivativeOn μ Ω v u' g' := by
  intro φ hφ hs hsub
  have hl : (∫ x, inner ℝ (g x) (φ x) ∂μ) = ∫ x, inner ℝ (g' x) (φ x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hh] with x hx
    by_cases hxs : x ∈ tsupport φ
    · rw [hx (hsub hxs)]
    · simp [image_eq_zero_of_notMem_tsupport hxs]
  have hr : (∫ x, inner ℝ (u x) (fderiv ℝ φ x v) ∂μ) =
      ∫ x, inner ℝ (u' x) (fderiv ℝ φ x v) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    by_cases hxs : x ∈ tsupport φ
    · rw [hx (hsub hxs)]
    · have hd : fderiv ℝ φ x = 0 := by
        by_contra hd
        exact hxs ((support_fderiv_subset ℝ) hd)
      simp [hd]
  rw [← hl, ← hr]
  exact hg φ hφ hs hsub

omit [BorelSpace X] [SecondCountableTopology X] in
theorem HasWeakDirectionalDerivativeOn.mono {Ω Ω' : Set X} {v : X} {u g : X → E}
    (hg : HasWeakDirectionalDerivativeOn μ Ω v u g) (hsub : Ω' ⊆ Ω) :
    HasWeakDirectionalDerivativeOn μ Ω' v u g :=
  fun φ hφ hs hφsub ↦ hg φ hφ hs (hφsub.trans hsub)

variable [CompleteSpace E] [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ]

omit [BorelSpace X] [SecondCountableTopology X] [CompleteSpace E] [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ] in
theorem HasWeakDirectionalDerivative.on
    {Ω : Set X} {v : X} {u g : X → E}
    (hg : HasWeakDirectionalDerivative μ v u g) :
    HasWeakDirectionalDerivativeOn μ Ω v u g :=
  fun φ hφ hs _ ↦ hg φ hφ hs

omit [CompleteSpace E] [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ] in
/-- A derivative of the localized field is the actual local derivative
on every region where its cutoff is one. -/
theorem HasWeakDirectionalDerivative.cutoff_eq_one
    {Ω : Set X} {η : X → ℝ} (hη : Continuous η) {M : ℝ}
    (hM : ∀ x, |η x| ≤ M) (hone : ∀ x ∈ Ω, η x = 1)
    {v : X} {u : Lp E 2 μ} {g : X → E}
    (hg : HasWeakDirectionalDerivative μ v (cutoffL2 η hη hM u) g) :
    HasWeakDirectionalDerivativeOn μ Ω v u g := by
  intro φ hφ hs hsub
  rw [hg φ hφ hs]
  congr 1
  apply integral_congr_ae
  filter_upwards [cutoffL2_ae η hη hM u] with x hx
  by_cases hxs : x ∈ tsupport φ
  · rw [hx, hone x (hsub hxs), one_smul]
  · have hd : fderiv ℝ φ x = 0 := by
      by_contra hd
      exact hxs ((support_fderiv_subset ℝ) hd)
    simp [hd]

end OAI.Analysis.PDE.Weak
