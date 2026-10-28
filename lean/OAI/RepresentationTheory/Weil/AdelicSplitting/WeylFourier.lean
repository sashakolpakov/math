import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierIntertwiner
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylMatrixCoefficients

/-! # Weyl Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeylFourier.LocalAnalysis

noncomputable section

section

/-! Weyl coefficients are ordinary Fourier transforms of translated
products. The required products belong to the actual archimedean Bruhat space. -/

open _root_.MeasureTheory
open OAI.RepresentationTheory.Weil.UnitarySplitting.WeylMatrixCoefficients.Construction (weylMatrixCoefficient)
open scoped ComplexConjugate

theorem archimedean_shifted_product_mem
    {k : Type} [NormedField k] [NormedAlgebra ℝ k] [FiniteDimensional ℝ k] {N : ℕ}
    (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (q : Local.FunctionsMetaplectic.Construction.Position k N) :
    (fun x => f.val (x - q) * conj (u.val x)) ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := by
  obtain ⟨φ, hφ⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp f.property
  obtain ⟨χ, hχ⟩ := ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mp u.property
  let a := SchwartzMap.compSubConstCLM ℝ q φ
  let b := χ.postcompCLM Complex.conjCLE.toContinuousLinearMap
  refine ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr
    ⟨SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) a b, ?_⟩
  funext x
  rw [hφ, hχ]
  rfl

theorem weylMatrixCoefficient_fourier
    {k : Type} [NormedField k] [CharZero k] [MeasurableSpace k] {N : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N))
    (f u : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (q p : Local.FunctionsMetaplectic.Construction.Position k N) :
    UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f u (Sum.elim q p) =
      ψ (-(Local.FunctionsMetaplectic.Construction.dot p q / 2)) * Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun x => f (x - q) * conj (u x)) (-p) := by
  unfold UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [Local.FunctionsMetaplectic.Construction.heisenbergFunction]
    have hp : (∑ i, (Sum.elim q p) (Sum.inr i) *
        (x i - (Sum.elim q p) (Sum.inl i) / 2)) = -(Local.FunctionsMetaplectic.Construction.dot p q / 2) + -Local.FunctionsMetaplectic.Construction.dot (-p) x := by
      simp only [Sum.elim_inr, Sum.elim_inl, Local.FunctionsMetaplectic.Construction.dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
        neg_neg, mul_sub, mul_div_assoc, Finset.sum_sub_distrib, Finset.sum_div]
      ring
    rw [hp, ψ.map_add_eq_mul]
    have hs : (fun i => x i - Sum.elim q p (Sum.inl i)) = x - q := rfl
    rw [hs]
    ring

end

/-! Weyl coefficient orthogonality at archimedean places follows from
the already proved coordinate Fourier Plancherel theorem. -/

open _root_.MeasureTheory
open OAI.RepresentationTheory.Weil.UnitarySplitting.WeylMatrixCoefficients.Construction (weylMatrixCoefficient)
open scoped ComplexConjugate

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]

theorem translatedNormProduct_integrable (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Integrable (fun z : Local.FunctionsMetaplectic.Construction.Position k N × Local.FunctionsMetaplectic.Construction.Position k N =>
      ‖f.val (z.2 - z.1)‖ ^ 2 * ‖u.val z.2‖ ^ 2) (μ.prod μ) := by
  have hfc := TestSpace.LocalAnalysis.schwartzBruhat_continuous f.property
  have huc := TestSpace.LocalAnalysis.schwartzBruhat_continuous u.property
  have hfi := TestSpace.LocalAnalysis.schwartzBruhat_norm_sq_integrable μ f
  have hui := TestSpace.LocalAnalysis.schwartzBruhat_norm_sq_integrable μ u
  apply (integrable_prod_iff' (show AEStronglyMeasurable
    (fun z : Local.FunctionsMetaplectic.Construction.Position k N × Local.FunctionsMetaplectic.Construction.Position k N => ‖f.val (z.2 - z.1)‖ ^ 2 * ‖u.val z.2‖ ^ 2)
    (μ.prod μ) from (by fun_prop : Continuous _).aestronglyMeasurable)).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => ?_), ?_⟩
  · simpa only using! (hfi.comp_sub_left x).mul_const (‖u.val x‖ ^ 2)
  have he (x : Local.FunctionsMetaplectic.Construction.Position k N) :
      (∫ q, ‖‖f.val (x - q)‖ ^ 2 * ‖u.val x‖ ^ 2‖ ∂μ) =
        (∫ q, ‖f.val q‖ ^ 2 ∂μ) * ‖u.val x‖ ^ 2 := by
    simp only [norm_mul, norm_pow, norm_norm]
    rw [integral_mul_const, integral_sub_left_eq_self (fun q => ‖f.val q‖ ^ 2) μ x]
  simp_rw [he]
  exact hui.const_mul _

theorem translatedNormProduct_integral (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (∫ q, ∫ x, ‖f.val (x - q)‖ ^ 2 * ‖u.val x‖ ^ 2 ∂μ ∂μ) =
      (∫ q, ‖f.val q‖ ^ 2 ∂μ) * ∫ x, ‖u.val x‖ ^ 2 ∂μ := by
  rw [integral_integral_swap (translatedNormProduct_integrable μ f u)]
  simp_rw [integral_mul_const, integral_sub_left_eq_self (fun q => ‖f.val q‖ ^ 2) μ]
  exact integral_const_mul _ _

variable [CharZero k] [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
variable (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)
variable (hStable : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N, Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)
variable (hInv : ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) x,
  Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x = f.val (-x))

include hu hc hStable hInv in
theorem weylCoefficient_momentum_energy (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (q : Local.FunctionsMetaplectic.Construction.Position k N) :
    (∫ p, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val u.val (Sum.elim q p)‖ ^ 2 ∂μ) =
      ∫ x, ‖f.val (x - q)‖ ^ 2 * ‖u.val x‖ ^ 2 ∂μ := by
  let a : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := ⟨_, archimedean_shifted_product_mem f u q⟩
  simp_rw [weylMatrixCoefficient_fourier, norm_mul, hu, one_mul]
  rw [integral_neg_eq_self (fun p => ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ a.val p‖ ^ 2) μ,
    FourierIntertwiner.LocalAnalysis.fourierIntegral_norm_sq ψ hu hc μ hStable hInv a]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change ‖f.val (x - q) * conj (u.val x)‖ ^ 2 = _
    rw [norm_mul, RCLike.norm_conj, mul_pow]

include hu hStable in
theorem weylCoefficient_momentum_integrable (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (q : Local.FunctionsMetaplectic.Construction.Position k N) :
    Integrable (fun p => ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val u.val (Sum.elim q p)‖ ^ 2) μ := by
  let a : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := ⟨_, archimedean_shifted_product_mem f u q⟩
  let b : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := ⟨_, hStable a⟩
  have hi := (TestSpace.LocalAnalysis.schwartzBruhat_norm_sq_integrable μ b).comp_neg
  simpa only [weylMatrixCoefficient_fourier, norm_mul, hu, one_mul] using! hi

include hu hc hStable hInv in
theorem weylCoefficient_product_energy (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (∫ z : Local.FunctionsMetaplectic.Construction.Position k N × Local.FunctionsMetaplectic.Construction.Position k N,
      ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val u.val (Sum.elim z.1 z.2)‖ ^ 2 ∂μ.prod μ) =
      (∫ x, ‖f.val x‖ ^ 2 ∂μ) * ∫ x, ‖u.val x‖ ^ 2 ∂μ := by
  have hcont : Continuous (fun z : Local.FunctionsMetaplectic.Construction.Position k N × Local.FunctionsMetaplectic.Construction.Position k N =>
      ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val u.val (Sum.elim z.1 z.2)‖ ^ 2) :=
    ((UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient_continuous ψ hc hu μ f u).comp
      (continuous_pi fun i => by cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
        fun_prop)).norm.pow 2
  have hi : Integrable (fun z : Local.FunctionsMetaplectic.Construction.Position k N × Local.FunctionsMetaplectic.Construction.Position k N =>
      ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val u.val (Sum.elim z.1 z.2)‖ ^ 2) (μ.prod μ) := by
    apply (integrable_prod_iff hcont.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (weylCoefficient_momentum_integrable μ ψ hu hStable f u), ?_⟩
    change Integrable (fun q => ∫ p,
      ‖‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val u.val (Sum.elim q p)‖ ^ 2‖ ∂μ) μ
    simp only [norm_pow, norm_norm]
    simp_rw [weylCoefficient_momentum_energy μ ψ hu hc hStable hInv]
    exact (translatedNormProduct_integrable μ f u).integral_prod_left
  rw [integral_prod _ hi]
  simp_rw [weylCoefficient_momentum_energy μ ψ hu hc hStable hInv]
  exact translatedNormProduct_integral μ f u

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeylFourier.LocalAnalysis
