import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier
import OAI.RepresentationTheory.Theta.RealPoisson

/-! # Coset Poisson -/

namespace OAI.RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction

noncomputable section

section

/-! Rational points in a finite-adelic lattice coset form an ordinary rational grid. -/

open scoped Classical

variable {ι : Type*}

def rationalGrid (q : ℚ) (a : ι → ℚ) (m : ι → ℤ) : ι → ℚ :=
  fun i => a i + q * (m i : ℚ)

theorem rationalGrid_injective (q : ℚ) (hq : q ≠ 0) (a : ι → ℚ) :
    Function.Injective (rationalGrid q a) := by
  intro m k h
  funext i
  have hi := congrFun h i
  change a i + q * (m i : ℚ) = a i + q * (k i : ℚ) at hi
  have heq := mul_left_cancel₀ hq (add_left_cancel hi)
  exact_mod_cast heq

theorem rational_finiteCoset_mem_iff (q : ℚ) (hq : q ≠ 0) (a x : ι → ℚ) :
    PoissonAutomorphyNormalizationData.finiteDiagonal x - PoissonAutomorphyNormalizationData.finiteDiagonal a ∈ PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq ↔
      ∃ m : ι → ℤ, rationalGrid q a m = x := by
  rw [PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff]
  change (∀ i, algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q⁻¹ *
    (algebraMap ℚ PoissonAutomorphyNormalizationData.AQf (x i) - algebraMap ℚ PoissonAutomorphyNormalizationData.AQf (a i)) ∈ AdelicSupport.PoissonAutomorphyConstruction.integralAdele) ↔ _
  simp only [← map_sub, ← map_mul, AdelicSupport.PoissonAutomorphyConstruction.rational_integral_iff]
  constructor
  · intro h
    choose m hm using h
    refine ⟨m, funext fun i => ?_⟩
    change a i + q * (m i : ℚ) = x i
    rw [hm i, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
    ring
  · rintro ⟨m, rfl⟩ i
    refine ⟨m i, ?_⟩
    simp only [rationalGrid, add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

theorem rationalReal_grid (q : ℚ) (a : ι → ℚ) (m : ι → ℤ) :
    PoissonAutomorphyNormalizationData.Construction.rationalReal (rationalGrid q a m) = PoissonAutomorphyNormalizationData.Construction.rationalReal a + (q : ℝ) • RealFourier.PoissonAutomorphyConstruction.integerReal m := by
  ext i
  simp [PoissonAutomorphyNormalizationData.Construction.rationalReal, rationalGrid, RealFourier.PoissonAutomorphyConstruction.integerReal]

theorem rational_coset_sum (q : ℚ) (hq : q ≠ 0) (a : ι → ℚ) (F : (ι → ℚ) → ℂ) :
    (∑' x : ι → ℚ, F x * PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq (PoissonAutomorphyNormalizationData.finiteDiagonal a) (PoissonAutomorphyNormalizationData.finiteDiagonal x)) =
      ∑' m : ι → ℤ, F (rationalGrid q a m) := by
  have hs : Function.support (fun x : ι → ℚ =>
      F x * PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq (PoissonAutomorphyNormalizationData.finiteDiagonal a) (PoissonAutomorphyNormalizationData.finiteDiagonal x)) ⊆
      Set.range (rationalGrid q a) := by
    intro x hx
    have hmem : PoissonAutomorphyNormalizationData.finiteDiagonal x - PoissonAutomorphyNormalizationData.finiteDiagonal a ∈ PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq := by
      by_contra h
      have hz : PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq (PoissonAutomorphyNormalizationData.finiteDiagonal a) (PoissonAutomorphyNormalizationData.finiteDiagonal x) = 0 :=
        PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem q hq h
      exact hx (by dsimp only; rw [hz, mul_zero])
    exact (rational_finiteCoset_mem_iff q hq a x).mp hmem
  rw [← (rationalGrid_injective q hq a).tsum_eq hs]
  apply tsum_congr
  intro m
  have hmem := (rational_finiteCoset_mem_iff q hq a (rationalGrid q a m)).mpr ⟨m, rfl⟩
  change F (rationalGrid q a m) * PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq
    (PoissonAutomorphyNormalizationData.finiteDiagonal (rationalGrid q a m) - PoissonAutomorphyNormalizationData.finiteDiagonal a) = _
  rw [PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_mem q hq hmem, mul_one]

theorem rational_lattice_sum (q : ℚ) (hq : q ≠ 0) (F : (ι → ℚ) → ℂ) :
    (∑' x : ι → ℚ, F x * PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq (PoissonAutomorphyNormalizationData.finiteDiagonal x)) =
      ∑' m : ι → ℤ, F (rationalGrid q 0 m) := by
  have h := rational_coset_sum q hq (0 : ι → ℚ) F
  have hz : PoissonAutomorphyNormalizationData.finiteDiagonal (0 : ι → ℚ) = 0 := by ext i; simp [PoissonAutomorphyNormalizationData.finiteDiagonal]
  simpa only [PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator, hz, sub_zero] using h

end

/-! Adelic Poisson summation for a rational finite-lattice coset. -/

open scoped Classical
open _root_.MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem finiteCharacter_rational_apply (q : ℚ) :
    D.finiteCharacter (algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q) = PoissonAutomorphyNormalizationData.standardRealCharacter (-(q : ℝ)) := by
  have hn : PoissonAutomorphyNormalizationData.standardRealCharacter (q : ℝ) ≠ 0 := by
    intro h
    have hh := PoissonAutomorphyNormalizationData.standardRealCharacter_unitary (q : ℝ)
    rw [h, norm_zero] at hh
    exact zero_ne_one hh
  apply mul_left_cancel₀ hn
  rw [PoissonAutomorphyFiniteFourier.Construction.character_rational_product D, ← AddChar.map_add_eq_mul, add_neg_cancel,
    AddChar.map_zero_eq_one]

theorem finiteCharacter_negative_rational_pairing (x a : ι → ℚ) :
    D.finiteCharacter (-(∑ i, PoissonAutomorphyNormalizationData.finiteDiagonal x i * PoissonAutomorphyNormalizationData.finiteDiagonal a i)) =
      PoissonAutomorphyNormalizationData.standardRealCharacter (∑ i, PoissonAutomorphyNormalizationData.Construction.rationalReal x i * PoissonAutomorphyNormalizationData.Construction.rationalReal a i) := by
  have heq : -(∑ i, PoissonAutomorphyNormalizationData.finiteDiagonal x i * PoissonAutomorphyNormalizationData.finiteDiagonal a i) =
      algebraMap ℚ PoissonAutomorphyNormalizationData.AQf (-(∑ i, x i * a i)) := by
    simp only [map_neg, map_sum, map_mul, PoissonAutomorphyNormalizationData.finiteDiagonal]
  rw [heq, finiteCharacter_rational_apply]
  simp only [Rat.cast_neg, Rat.cast_sum, Rat.cast_mul, neg_neg, PoissonAutomorphyNormalizationData.Construction.rationalReal]

theorem coset_poisson_summation (n : ℕ) (hn : 0 < n) (a : ι → ℚ)
    (f : SchwartzMap (ι → ℝ) ℂ) :
    (∑' x : ι → ℚ, f (PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
      PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator (n : ℚ) (by exact_mod_cast hn.ne') (PoissonAutomorphyNormalizationData.finiteDiagonal a) (PoissonAutomorphyNormalizationData.finiteDiagonal x)) =
    ∑' x : ι → ℚ, PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f (PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
      PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure
        (PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator (n : ℚ) (by exact_mod_cast hn.ne') (PoissonAutomorphyNormalizationData.finiteDiagonal a)) (PoissonAutomorphyNormalizationData.finiteDiagonal x) := by
  let hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  let v : ℂ := ((n : ℝ) ^ Fintype.card ι)⁻¹
  calc
    _ = ∑' m : ι → ℤ, f (PoissonAutomorphyNormalizationData.Construction.rationalReal a + (n : ℝ) • RealFourier.PoissonAutomorphyConstruction.integerReal m) := by
      rw [rational_coset_sum]
      simp only [rationalReal_grid, Rat.cast_natCast]
    _ = v * ∑' k : ι → ℤ, PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f
        ((n : ℝ)⁻¹ • RealFourier.PoissonAutomorphyConstruction.integerReal k) * PoissonAutomorphyNormalizationData.standardRealCharacter
          (∑ i, (k i : ℝ) * ((n : ℝ)⁻¹ * PoissonAutomorphyNormalizationData.Construction.rationalReal a i)) :=
      by simpa only [v, Complex.ofReal_inv, Complex.ofReal_pow] using
        RealPoisson.AutomorphyConstruction.real_poisson_summation_scaled (n : ℝ) (by exact_mod_cast hn) f (PoissonAutomorphyNormalizationData.Construction.rationalReal a)
    _ = v * ∑' x : ι → ℚ,
        (PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f (PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
          D.finiteCharacter (-(∑ i, PoissonAutomorphyNormalizationData.finiteDiagonal x i * PoissonAutomorphyNormalizationData.finiteDiagonal a i))) *
            PoissonAutomorphyFiniteFourier.Construction.latticeIndicator (n : ℚ)⁻¹ (inv_ne_zero hnq) (PoissonAutomorphyNormalizationData.finiteDiagonal x) := by
      congr 1
      rw [rational_lattice_sum]
      apply tsum_congr
      intro k
      rw [finiteCharacter_negative_rational_pairing D]
      have hreal : PoissonAutomorphyNormalizationData.Construction.rationalReal (rationalGrid (n : ℚ)⁻¹ 0 k) =
          (n : ℝ)⁻¹ • RealFourier.PoissonAutomorphyConstruction.integerReal k := by
        ext i
        simp [PoissonAutomorphyNormalizationData.Construction.rationalReal, rationalGrid, RealFourier.PoissonAutomorphyConstruction.integerReal]
      rw [hreal]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul, RealFourier.PoissonAutomorphyConstruction.integerReal]
      ring
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro x
      rw [PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator_fourier D, PoissonAutomorphyFiniteFourier.Construction.finiteLattice_nat_volume D n hn]
      dsimp [v]
      push_cast
      ring

end

end OAI.RepresentationTheory.Theta.CosetPoisson.AutomorphyConstruction
