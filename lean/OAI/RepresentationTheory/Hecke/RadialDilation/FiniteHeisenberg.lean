import OAI.RepresentationTheory.Theta.CosetTests

/-! # Finite Heisenberg -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization

noncomputable section

/-! Heisenberg invariance determines each finite-adelic lattice vector. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

def CommutesFiniteHeisenberg (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (T : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) : Prop :=
  ∀ (p q : ι → Theta.PoissonAutomorphyNormalizationData.AQf) (f h : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι),
    (∀ x, h.val x = Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p q f.val x) →
    ∀ x, (T h).val x = Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p q (T f).val x

theorem finite_heisenberg_translation (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (q x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) (f : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) :
    Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter 0 q f x = f (x - q) := by
  simp [Theta.PoissonAutomorphyNormalizationData.heisenberg]
  rfl

theorem finite_heisenberg_modulation (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (p x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) (f : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) :
    Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p 0 f x = D.finiteCharacter (∑ i, p i * x i) * f x := by
  simp [Theta.PoissonAutomorphyNormalizationData.heisenberg]

theorem finite_lattice_annihilator (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (q : ℚ) (hq : q ≠ 0) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    x ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq ↔
      ∀ p ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq), D.finiteCharacter (∑ i, p i * x i) = 1 := by
  constructor
  · intro hx p hp
    have h := Theta.PoissonAutomorphyFiniteFourier.Construction.finiteCharacter_pairing_dual_lattice D q hq
      ((Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq)).neg_mem hp) hx
    simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg] using h
  · intro h
    rw [Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff]
    intro i
    let p := Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q⁻¹ (Pi.single i (1 : Theta.PoissonAutomorphyNormalizationData.AQf))
    have hp : p ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq) := by
      refine ⟨Pi.single i 1, ?_, rfl⟩
      intro j
      by_cases hj : j = i <;> simp [hj, Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.one_mem, Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.zero_mem]
    have he : (∑ j, p j * x j) = algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf q⁻¹ * x i := by
      simp [p, Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale, Pi.single_apply]
    have hh := h p hp
    rw [he] at hh
    exact (Theta.PoissonAutomorphyFiniteFourier.Construction.finiteCharacter_eq_one_iff D _).mp hh

omit [DecidableEq ι] in
theorem latticeTestFunction_translation (q : ℚ) (hq : q ≠ 0)
    (a : ι → Theta.PoissonAutomorphyNormalizationData.AQf) (ha : a ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq).val (x - a) = (Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq).val x := by
  change Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq (x - a) = Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq x
  rw [sub_eq_add_neg, add_comm]
  exact Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_add q hq ((Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq).neg_mem ha) x

theorem commuting_operator_lattice_eigenvector (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (T : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (hT : CommutesFiniteHeisenberg D T)
    (q : ℚ) (hq : q ≠ 0) :
    T (Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq) =
      (T (Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq)).val 0 • Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq := by
  let f := Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (ι := ι) q hq
  have hmod (p : ι → Theta.PoissonAutomorphyNormalizationData.AQf) (hp : p ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q⁻¹ (inv_ne_zero hq)) (x : ι → Theta.PoissonAutomorphyNormalizationData.AQf) :
      (T f).val x = D.finiteCharacter (∑ i, p i * x i) * (T f).val x := by
    have hfix (y : ι → Theta.PoissonAutomorphyNormalizationData.AQf) : f.val y = Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p 0 f.val y := by
      rw [finite_heisenberg_modulation]
      by_cases hy : y ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq
      · rw [(finite_lattice_annihilator D q hq y).mp hy p hp, one_mul]
      · change Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq y = _ * Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq y
        rw [Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem q hq hy, mul_zero]
    simpa only [finite_heisenberg_modulation] using hT p 0 f f hfix x
  apply Subtype.ext
  funext x
  change (T f).val x = (T f).val 0 * f.val x
  by_cases hx : x ∈ Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq
  · have hfix (y : ι → Theta.PoissonAutomorphyNormalizationData.AQf) : f.val y = Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter 0 x f.val y := by
      rw [finite_heisenberg_translation]
      exact (latticeTestFunction_translation q hq x hx y).symm
    have h := hT 0 x f f hfix x
    rw [finite_heisenberg_translation, sub_self] at h
    change (T f).val x = (T f).val 0 * Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq x
    rw [Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_mem q hq hx, mul_one]
    exact h
  · have hz : (T f).val x = 0 := by
      by_contra hn
      apply hx
      apply (finite_lattice_annihilator D q hq x).mpr
      intro p hp
      exact (mul_eq_right₀ hn).mp (hmod p hp x).symm
    change (T f).val x = (T f).val 0 * Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq x
    rw [hz, Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator_of_notMem q hq hx, mul_zero]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization
