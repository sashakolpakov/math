import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LatticeEigenline

/-! # Schur -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Schur.CM

noncomputable section

/-! Scalar uniqueness for the constructed finite Heisenberg action,
proved on the full concrete test space using lattice coset expansions. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LatticeEigenline.CM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem commuting_operator_coset_eigenvector (T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (hT : LatticeEigenline.CM.CommutesFiniteHeisenberg T)
    (q : ℚ) (hq : q ≠ 0) (a : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) =
      (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq)).val 0 • RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a := by
  have hfix (x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a).val x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character 0 a (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq).val x := by
    rw [LatticeEigenline.CM.finite_heisenberg_translation]
    rfl
  apply Subtype.ext
  funext x
  have h := hT 0 a (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq) (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) hfix x
  rw [LatticeEigenline.CM.finite_heisenberg_translation, LatticeEigenline.CM.commuting_operator_lattice_eigenvector T hT] at h
  exact h

theorem commuting_operator_periodic_eigenvector (T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (hT : LatticeEigenline.CM.CommutesFiniteHeisenberg T)
    (q : ℚ) (hq : q ≠ 0) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (hp : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq, ∀ x, φ.val (u + x) = φ.val x) :
    T φ = (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq)).val 0 • φ := by
  obtain ⟨s, hs⟩ := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_coset_expansion φ q hq hp
  let a : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.FiniteQuotient (ι := ι) q hq → (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
    fun c => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep q hq c)
  have hφ : φ = ∑ c ∈ s, φ.val (a c) • RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq (a c) := by
    apply Subtype.ext
    funext x
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest_apply] using hs x
  rw [hφ, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_smul, commuting_operator_coset_eigenvector T hT, smul_smul, smul_smul, mul_comm]

/-- A linear operator commuting with finite-adelic translations and
modulations is one scalar on the full, concrete test space. -/
theorem finite_heisenberg_commutant_scalar (T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (hT : LatticeEigenline.CM.CommutesFiniteHeisenberg T) :
    ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι, T φ = (T RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction).val 0 • φ := by
  intro φ
  obtain ⟨n, hn, hp⟩ := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_lattice_period φ
  let hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have href : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (n : ℚ) hq, ∀ x,
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction (ι := ι)).val (u + x) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction.val x := by
    intro u hu x
    exact RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_add (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_nat_subset_integral n hn hu) x
  have h := commuting_operator_periodic_eigenvector T hT (n : ℚ) hq RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction href
  have he := congrArg (fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι => f.val 0) h
  change (T RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction).val 0 =
    (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (n : ℚ) hq)).val 0 * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator 0 at he
  rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem, mul_one] at he
  rw [he]
  exact commuting_operator_periodic_eigenvector T hT (n : ℚ) hq φ hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Schur.CM
