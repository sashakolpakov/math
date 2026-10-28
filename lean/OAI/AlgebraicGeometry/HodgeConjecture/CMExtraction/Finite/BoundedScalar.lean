import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg

/-! # Bounded Scalar -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BoundedScalar.TestTransport

noncomputable section

section

/-! The exact joint translation and modulation eigenline associated
with a rational lattice in the actual finite adeles. -/

open scoped Classical _root_.Matrix

open OAI.RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization

variable {I : Type*} [Fintype I] [DecidableEq I]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)

theorem finite_lattice_joint_eigenfunction (q : ℚ) (hq : q ≠ 0)
    (f : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ)
    (hmod : ∀ p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq), ∀ x,
      f x = D.finiteCharacter (∑ i, p i * x i) * f x)
    (htrans : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq, ∀ x, f (x - u) = f x) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    f x = f 0 * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq x := by
  by_cases hx : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq
  · rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_mem q hq hx, mul_one]
    simpa only [sub_self] using (htrans x hx x).symm
  · have hz : f x = 0 := by
      by_contra hn
      apply hx
      apply (RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization.finite_lattice_annihilator D q hq x).mpr
      intro p hp
      exact (mul_eq_right₀ hn).mp (hmod p hp x).symm
    rw [hz, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem q hq hx, mul_zero]

theorem finite_lattice_joint_eigenvector (q : ℚ) (hq : q ≠ 0) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (hmod : ∀ p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq), ∀ x,
      f.val x = D.finiteCharacter (∑ i, p i * x i) * f.val x)
    (htrans : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq, ∀ x, f.val (x - u) = f.val x) :
    f = f.val 0 • RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq := by
  apply Subtype.ext
  funext x
  exact finite_lattice_joint_eigenfunction D q hq f.val hmod htrans x

end

/-! A finite operator acts by one scalar on all integral, periodic
tests once its reference lattice vector and its integral translates
have the prescribed Heisenberg behavior. -/

open scoped Classical _root_.Matrix

open OAI.RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization

variable {I : Type*} [Fintype I] [DecidableEq I]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (N : ℕ) (hN : 0 < N)
  (T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)

theorem finite_integral_periodic_operator_scalar
    (hmod : ∀ p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hN.ne')), ∀ x,
      (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (N : ℚ) (by exact_mod_cast hN.ne'))).val x =
        D.finiteCharacter (∑ i, p i * x i) *
          (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (N : ℚ) (by exact_mod_cast hN.ne'))).val x)
    (htrans : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'), ∀ x,
      (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (N : ℚ) (by exact_mod_cast hN.ne'))).val (x - u) =
        (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (N : ℚ) (by exact_mod_cast hN.ne'))).val x)
    (hcoset : ∀ a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors, ∀ x,
      (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest (N : ℚ) (by exact_mod_cast hN.ne') a)).val x =
        (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (N : ℚ) (by exact_mod_cast hN.ne'))).val (x - a))
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'), ∀ x,
      φ.val (u + x) = φ.val x) :
    T φ = (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (N : ℚ) (by exact_mod_cast hN.ne'))).val 0 • φ := by
  let q : ℚ := N
  have hq : q ≠ 0 := by
    change (N : ℚ) ≠ 0
    exact_mod_cast hN.ne'
  let c := (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq)).val 0
  have hcos (a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (ha : a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors) :
      T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) = c • RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a := by
    apply Subtype.ext
    funext x
    exact (hcoset a ha x).trans
      (finite_lattice_joint_eigenfunction D q hq (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq)).val hmod htrans (x - a))
  obtain ⟨s, hs⟩ := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_coset_expansion φ q hq hperiod
  let a := fun z : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.FiniteQuotient (ι := I) q hq => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep q hq z)
  have hφ : φ = ∑ z ∈ s, φ.val (a z) • RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq (a z) := by
    apply Subtype.ext
    funext x
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest_apply] using hs x
  change T φ = c • φ
  rw [hφ, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul]
  by_cases hzero : φ.val (a z) = 0
  · simp only [hzero, zero_smul, smul_zero]
  · have ha : a z ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors := by
      by_contra hn
      exact hzero (hsupport _ hn)
    rw [hcos _ ha, smul_smul, smul_smul, mul_comm]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BoundedScalar.TestTransport
