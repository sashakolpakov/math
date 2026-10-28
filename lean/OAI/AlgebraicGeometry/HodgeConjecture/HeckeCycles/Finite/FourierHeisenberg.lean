import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierOperator
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LatticeVolumes

/-! # Fourier Heisenberg -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM.Inversion

/-! Fourier inversion for the constructed finite Haar measure, first
on lattice cosets and then on every actual finite Schwartz function. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierOperator.CM

variable {I : Type*} [Fintype I]

omit [Fintype I] in
theorem latticeIndicator_neg (q : ℚ) (hq : q ≠ 0) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq (-x) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq x := by
  simp only [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator, Set.indicator, SetLike.mem_coe, AddSubgroup.neg_mem_iff]

theorem coset_double_fourier (q : ℚ) (hq : q ≠ 0) (a x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (FourierOperator.CM.fourierMap (FourierOperator.CM.fourierMap (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a))).val x =
      (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a).val (-x) := by
  let ψ := Constructed.AdelicCharacter.CM.Finite.character
  let v := (Constructed.FiniteMeasure.CM.measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q hq : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))
  have hf : (FourierOperator.CM.fourierMap (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a)).val = fun y =>
      ψ (-(∑ i, y i * a i)) * ((v : ℂ) * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q⁻¹ (inv_ne_zero hq) y) := by
    funext y
    exact Constructed.FiniteFourier.CM.latticeCosetIndicator_fourier q hq a y
  rw [FourierOperator.CM.fourierMap_apply, hf]
  have hi : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ (Constructed.FiniteMeasure.CM.measure I)
      (fun y => ψ (-(∑ i, y i * a i)) * ((v : ℂ) * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q⁻¹ (inv_ne_zero hq) y)) x =
      (v : ℂ) * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier ψ (Constructed.FiniteMeasure.CM.measure I) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q⁻¹ (inv_ne_zero hq)) (x + a) := by
    rw [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      have hp : ψ (-(∑ i, (x + a) i * y i)) =
          ψ (-(∑ i, y i * a i)) * ψ (-(∑ i, x i * y i)) := by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_add,
          AddChar.map_add_eq_mul]
        simp only [mul_comm]
      dsimp only
      rw [hp]
      ring
  rw [hi, Constructed.FiniteFourier.CM.latticeIndicator_fourier]
  simp only [inv_inv]
  rw [← mul_assoc]
  have hv : (v : ℂ) *
      ((Constructed.FiniteMeasure.CM.measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q⁻¹ (inv_ne_zero hq) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : ℂ) = 1 := by
    exact_mod_cast LatticeVolumes.CM.reciprocal_volumes (I := I) q hq
  rw [hv, one_mul]
  change RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq (x + a) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq (-x - a)
  rw [show -x - a = -(x + a) by abel, latticeIndicator_neg]

theorem double_fourier (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (FourierOperator.CM.fourierMap (FourierOperator.CM.fourierMap f)).val x = f.val (-x) := by
  obtain ⟨n, hn, s, hf⟩ := RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.finiteSchwartz_coset_expansion_eq f
  rw [hf]
  simp only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, coset_double_fourier]

theorem self_dual (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.Finite.character (Constructed.FiniteMeasure.CM.measure I)
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.Finite.character (Constructed.FiniteMeasure.CM.measure I) f.val) x = f.val (-x) :=
  double_fourier f x

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM.Inversion

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM.Equiv

/-! The actual finite Fourier operator is invertible. Its inverse is
its third power, since the square is reflection and the fourth power
is the identity. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierOperator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM.Inversion

variable {I : Type*} [Fintype I]

theorem fourth_fourier (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    FourierOperator.CM.fourierMap (FourierOperator.CM.fourierMap (FourierOperator.CM.fourierMap (FourierOperator.CM.fourierMap f))) = f := by
  apply Subtype.ext
  funext x
  rw [Inversion.double_fourier, Inversion.double_fourier, neg_neg]

def fourierEquiv : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I where
  toLinearMap := FourierOperator.CM.fourierMap
  invFun f := FourierOperator.CM.fourierMap (FourierOperator.CM.fourierMap (FourierOperator.CM.fourierMap f))
  left_inv := fourth_fourier
  right_inv := fourth_fourier

theorem fourierEquiv_apply (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (fourierEquiv f).val x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.Finite.character (Constructed.FiniteMeasure.CM.measure I) f.val x := rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM.Equiv

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM
open scoped Classical
section

/-! Actual finite Heisenberg translations preserve the finite Schwartz
space for the constructed additive character. -/

variable {I : Type*} [Fintype I]

theorem heisenberg_mem (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p q f.val ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I := by
  obtain ⟨hf, hc⟩ := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff f.val).mp f.property
  have hp : Continuous (fun x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf =>
      ∑ i, p i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q i)) :=
    continuous_finsetSum Finset.univ (fun i _ =>
      continuous_const.mul ((continuous_apply i).sub continuous_const))
  have ht : Continuous (fun x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => fun i => x i - q i) :=
    continuous_pi fun i => (continuous_apply i).sub continuous_const
  apply (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
  constructor
  · exact (Constructed.AdelicCharacter.CM.Finite.character_locallyConstant.comp_continuous hp).mul
      (hf.comp_continuous ht)
  · have hs : HasCompactSupport (fun x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => f.val (fun i => x i - q i)) := by
      have he : (fun x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => f.val (fun i => x i - q i)) =
          f.val ∘ Homeomorph.addRight (-q) := by
        funext x
        apply congrArg f.val
        funext i
        exact sub_eq_add_neg _ _
      rw [he]
      exact hc.comp_homeomorph (Homeomorph.addRight (-q))
    exact hs.mul_left

def operator (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I where
  toFun f := ⟨RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p q f.val,
    heisenberg_mem p q f⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact mul_left_comm _ _ _

theorem operator_apply (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (operator p q f).val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p q f.val x := rfl

theorem inverse_operator (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    operator (-p) (-q) (operator p q f) = f := by
  apply Subtype.ext
  funext x
  change Constructed.AdelicCharacter.CM.Finite.character _ *
    (Constructed.AdelicCharacter.CM.Finite.character _ * f.val _) = f.val x
  have hx : (fun i => x i - (-q) i - q i) = x := by
    funext i
    simp
  rw [hx, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have hp : (∑ i, (-p) i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * (-q) i)) +
      (∑ i, p i * ((x i - (-q) i) - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q i)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have hh : (2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) * algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) = 1 := by
      rw [← map_ofNat (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) 2, ← map_mul]
      norm_num
    simp only [Pi.neg_apply]
    linear_combination -(p i * q i) * hh
  rw [hp, AddChar.map_zero_eq_one, one_mul]

def equivalence (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I where
  toLinearMap := operator p q
  invFun := operator (-p) (-q)
  left_inv := inverse_operator p q
  right_inv f := by
    change operator p q (operator (-p) (-q) f) = f
    have h := inverse_operator (-p) (-q) f
    rw [neg_neg, neg_neg] at h
    exact h

end

/-! The constructed finite Fourier transform has the precise
Heisenberg covariance for the momentum-position Weyl matrix. -/

open scoped _root_.Matrix
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM.Equiv

variable {I : Type*} [Fintype I]

theorem half_two : (2 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) * algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) = 1 := by
  rw [← map_ofNat (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) 2, ← map_mul]
  norm_num

theorem phase_identity (p q x y : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (∑ i, p i * ((y i + q i) - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q i)) +
      (-(∑ i, x i * (y i + q i))) =
    (∑ i, (-q) i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * p i)) +
      (-(∑ i, (x i - p i) * y i)) := by
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Pi.neg_apply]
  apply Finset.sum_congr rfl
  intro i _
  linear_combination -(p i * q i) * half_two

theorem fourier_heisenberg (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.Finite.character (Constructed.FiniteMeasure.CM.measure I)
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p q f) x =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character (-q) p
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.Finite.character (Constructed.FiniteMeasure.CM.measure I) f) x := by
  let ψ := Constructed.AdelicCharacter.CM.Finite.character
  change (∫ y, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg ψ p q f y * ψ (-(∑ i, x i * y i)) ∂(Constructed.FiniteMeasure.CM.measure I)) = _
  rw [← integral_add_right_eq_self (μ := Constructed.FiniteMeasure.CM.measure I)
    (fun y => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg ψ p q f y * ψ (-(∑ i, x i * y i))) q]
  change (∫ y, (ψ (∑ i, p i * ((y + q) i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q i)) *
    f (fun i => (y + q) i - q i)) * ψ (-(∑ i, x i * (y + q) i)) ∂(Constructed.FiniteMeasure.CM.measure I)) =
      ψ (∑ i, (-q) i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * p i)) *
        ∫ y, f y * ψ (-(∑ i, (x i - p i) * y i)) ∂(Constructed.FiniteMeasure.CM.measure I)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    have hy : (fun i => (y + q) i - q i) = y := by funext i; simp
    rw [hy]
    simp only [Pi.add_apply]
    have hp := congrArg ψ (phase_identity p q x y)
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul] at hp
    calc
      _ = (ψ (∑ i, p i * ((y i + q i) - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q i)) *
          ψ (-(∑ i, x i * (y i + q i)))) * f y := by ring
      _ = _ := by rw [hp]; ring

def weyl : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := by
  refine ⟨Matrix.fromBlocks 0 (-1) 1 0, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp

theorem weyl_phase (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (weyl (I := I)).val *ᵥ Sum.elim p q = Sum.elim (-q) p := by
  funext i
  cases i <;>
    simp [weyl, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem intertwines : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg Constructed.AdelicCharacter.CM.Finite.character
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) weyl Equiv.fourierEquiv := by
  intro p q f h hh x
  rw [Equiv.fourierEquiv_apply, show h.val = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p q f.val
    from funext hh, fourier_heisenberg, weyl_phase]
  rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM

end

end OAI
