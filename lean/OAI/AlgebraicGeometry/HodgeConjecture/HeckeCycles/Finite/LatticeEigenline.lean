import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteFourier

/-! # Lattice Eigenline -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LatticeEigenline.CM

noncomputable section

/-! The exact constructed finite character determines the lattice
Heisenberg eigenline. The elementary lattice argument uses no Weil data. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def CommutesFiniteHeisenberg (T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) : Prop :=
  ∀ (p q : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι),
    (∀ x, h.val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p q f.val x) →
    ∀ x, (T h).val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p q (T f).val x

omit [DecidableEq ι] in
theorem finite_heisenberg_translation (q x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character 0 q f x = f (x - q) := by
  simp [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg]
  rfl

omit [DecidableEq ι] in
theorem finite_heisenberg_modulation (p x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p 0 f x = Constructed.AdelicCharacter.CM.Finite.character (∑ i, p i * x i) * f x := by
  simp [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg]

theorem finite_lattice_annihilator (q : ℚ) (hq : q ≠ 0) (x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq ↔
      ∀ p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq), Constructed.AdelicCharacter.CM.Finite.character (∑ i, p i * x i) = 1 := by
  constructor
  · intro hx p hp
    have h := Constructed.FiniteFourier.CM.finiteCharacter_pairing_dual_lattice q hq
      ((RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq)).neg_mem hp) hx
    simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg] using h
  · intro h
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff]
    intro i
    let p := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q⁻¹ (Pi.single i (1 : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))
    have hp : p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq) := by
      refine ⟨Pi.single i 1, ?_, rfl⟩
      intro j
      by_cases hj : j = i <;> simp [hj, RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.one_mem, RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.zero_mem]
    have he : (∑ j, p j * x j) = algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q⁻¹ * x i := by
      simp [p, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale, Pi.single_apply]
    have hh := h p hp
    rw [he] at hh
    exact (Constructed.AdelicCharacter.CM.Finite.character_eq_one_iff _).mp hh

omit [DecidableEq ι] in
theorem latticeTestFunction_translation (q : ℚ) (hq : q ≠ 0)
    (a : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (ha : a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq) (x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq).val (x - a) = (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq).val x := by
  change RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq (x - a) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq x
  rw [sub_eq_add_neg, add_comm]
  exact RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_add q hq ((RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq).neg_mem ha) x

theorem commuting_operator_lattice_eigenvector (T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (hT : CommutesFiniteHeisenberg T)
    (q : ℚ) (hq : q ≠ 0) :
    T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq) =
      (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq)).val 0 • RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq := by
  let f := RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (ι := ι) q hq
  have hmod (p : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hp : p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq)) (x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
      (T f).val x = Constructed.AdelicCharacter.CM.Finite.character (∑ i, p i * x i) * (T f).val x := by
    have hfix (y : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : f.val y = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p 0 f.val y := by
      rw [finite_heisenberg_modulation]
      by_cases hy : y ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq
      · rw [(finite_lattice_annihilator q hq y).mp hy p hp, one_mul]
      · change RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq y = _ * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq y
        rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem q hq hy, mul_zero]
    simpa only [finite_heisenberg_modulation] using hT p 0 f f hfix x
  apply Subtype.ext
  funext x
  change (T f).val x = (T f).val 0 * f.val x
  by_cases hx : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq
  · have hfix (y : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : f.val y = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character 0 x f.val y := by
      rw [finite_heisenberg_translation]
      exact (latticeTestFunction_translation q hq x hx y).symm
    have h := hT 0 x f f hfix x
    rw [finite_heisenberg_translation, sub_self] at h
    change (T f).val x = (T f).val 0 * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq x
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_mem q hq hx, mul_one]
    exact h
  · have hz : (T f).val x = 0 := by
      by_contra hn
      apply hx
      apply (finite_lattice_annihilator q hq x).mpr
      intro p hp
      exact (mul_eq_right₀ hn).mp (hmod p hp x).symm
    change (T f).val x = (T f).val 0 * RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq x
    rw [hz, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem q hq hx, mul_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LatticeEigenline.CM
