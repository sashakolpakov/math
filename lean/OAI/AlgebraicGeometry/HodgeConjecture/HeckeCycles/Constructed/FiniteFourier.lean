import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCharacter
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure
import OAI.RepresentationTheory.Theta.CosetTests

/-! # Finite Fourier -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteFourier.CM

noncomputable section

/-! Fourier transforms of lattice cosets for the constructed character
and Haar measure. These computations specialize the elementary PoissonAutomorphy
lattice arguments directly, without assuming a WeilData record. -/

open scoped Classical
open _root_.MeasureTheory OAI.RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM

variable {ι : Type*} [Fintype ι]

theorem pairing_integral {x y : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf}
    (hx : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors) (hy : y ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors) :
    AdelicCharacter.CM.Finite.character (-(∑ i, x i * y i)) = 1 := by
  apply AdelicCharacter.CM.Finite.character_integral
  exact RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.neg_mem (RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sum_mem (fun i _ => RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.mul_mem
    (hx i) (hy i)))

theorem finiteCharacter_pairing_dual_lattice (q : ℚ) (hq : q ≠ 0)
    {x y : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf} (hx : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq))
    (hy : y ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq) : AdelicCharacter.CM.Finite.character (-(∑ i, x i * y i)) = 1 := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  change AdelicCharacter.CM.Finite.character (-(∑ i, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q⁻¹ u i * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q v i)) = 1
  have heq (i : ι) : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q⁻¹ u i * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q v i = u i * v i := by
    dsimp [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale]
    calc
      _ = (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q⁻¹ * algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q) * (u i * v i) := by ring
      _ = _ := by rw [← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]
  simp only [heq]
  exact pairing_integral hu hv

theorem latticeIndicator_fourier_of_mem (q : ℚ) (hq : q ≠ 0) {x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf}
    (hx : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier AdelicCharacter.CM.Finite.character (FiniteMeasure.CM.measure ι) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq) x =
      ((FiniteMeasure.CM.measure ι).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := ι) q hq : Set (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : ℂ) := by
  have heq : (fun y => RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq y * AdelicCharacter.CM.Finite.character (-(∑ i, x i * y i))) =
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq := by
    funext y
    by_cases hy : y ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq
    · rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_mem q hq hy, finiteCharacter_pairing_dual_lattice q hq hx hy, one_mul]
    · rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem q hq hy, zero_mul]
  rw [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier, heq]
  change (∫ y, (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := ι) q hq : Set (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)).indicator
    (fun _ => (1 : ℂ)) y ∂(FiniteMeasure.CM.measure ι)) = _
  rw [integral_indicator (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_measurableSet q hq)]
  simp

theorem latticeIndicator_fourier_of_notMem (q : ℚ) (hq : q ≠ 0) {x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf}
    (hx : x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier AdelicCharacter.CM.Finite.character (FiniteMeasure.CM.measure ι) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq) x = 0 := by
  have hx' : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors := by
    simpa only [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff, inv_inv] using hx
  obtain ⟨i, hi⟩ : ∃ i, algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q * x i ∉ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := not_forall.mp hx'
  let v : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := Pi.single i 1
  let u := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q v
  have hu : u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq := by
    refine ⟨v, ?_, rfl⟩
    intro j
    by_cases hj : j = i <;> simp [v, hj, RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.one_mem, RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.zero_mem]
  have hpair : (∑ j, x j * u j) = algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q * x i := by
    calc
      _ = algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q * (∑ j, x j * v j) := by
        simp only [u, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [show (∑ j, x j * v j) = x i from dotProduct_single_one x i]
  have hphase : AdelicCharacter.CM.Finite.character (-(∑ j, x j * u j)) ≠ 1 := by
    rw [hpair]
    intro h
    exact hi (RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.neg_mem_iff.mp ((AdelicCharacter.CM.Finite.character_eq_one_iff _).mp h))
  let F := fun y : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq y * AdelicCharacter.CM.Finite.character (-(∑ j, x j * y j))
  have hshift (y : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : F (u + y) = AdelicCharacter.CM.Finite.character (-(∑ j, x j * u j)) * F y := by
    dsimp [F]
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_add q hq hu]
    simp only [mul_add, Finset.sum_add_distrib, neg_add, AddChar.map_add_eq_mul]
    ring
  have h := integral_add_left_eq_self (μ := FiniteMeasure.CM.measure ι) F u
  simp_rw [hshift, integral_const_mul] at h
  change AdelicCharacter.CM.Finite.character (-(∑ j, x j * u j)) *
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier AdelicCharacter.CM.Finite.character (FiniteMeasure.CM.measure ι) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq) x =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier AdelicCharacter.CM.Finite.character (FiniteMeasure.CM.measure ι) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq) x at h
  by_contra hn
  exact hphase ((mul_eq_right₀ hn).mp h)

theorem latticeIndicator_fourier (q : ℚ) (hq : q ≠ 0) (x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier AdelicCharacter.CM.Finite.character (FiniteMeasure.CM.measure ι) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq) x =
      ((FiniteMeasure.CM.measure ι).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := ι) q hq : Set (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : ℂ) *
        RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q⁻¹ (inv_ne_zero hq) x := by
  by_cases hx : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq)
  · rw [latticeIndicator_fourier_of_mem q hq hx,
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_mem q⁻¹ (inv_ne_zero hq) hx, mul_one]
  · rw [latticeIndicator_fourier_of_notMem q hq hx,
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem q⁻¹ (inv_ne_zero hq) hx, mul_zero]

theorem latticeCosetIndicator_fourier (q : ℚ) (hq : q ≠ 0) (a x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier AdelicCharacter.CM.Finite.character (FiniteMeasure.CM.measure ι) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq a) x =
      AdelicCharacter.CM.Finite.character (-(∑ i, x i * a i)) *
        (((FiniteMeasure.CM.measure ι).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := ι) q hq : Set (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : ℂ) *
          RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q⁻¹ (inv_ne_zero hq) x) := by
  rw [← latticeIndicator_fourier q hq x]
  change (∫ y, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq a y * AdelicCharacter.CM.Finite.character (-(∑ i, x i * y i))
    ∂(FiniteMeasure.CM.measure ι)) = _
  rw [← integral_add_right_eq_self (μ := FiniteMeasure.CM.measure ι)
    (fun y => RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq a y * AdelicCharacter.CM.Finite.character (-(∑ i, x i * y i))) a]
  calc
    _ = ∫ y, AdelicCharacter.CM.Finite.character (-(∑ i, x i * a i)) *
        (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq y * AdelicCharacter.CM.Finite.character (-(∑ i, x i * y i))) ∂(FiniteMeasure.CM.measure ι) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator]
        rw [add_sub_cancel_right]
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add, AddChar.map_add_eq_mul]
        ring
    _ = _ := integral_const_mul _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteFourier.CM
