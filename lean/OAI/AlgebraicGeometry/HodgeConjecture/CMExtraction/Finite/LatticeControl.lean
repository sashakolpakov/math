import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BoundedScalar

/-! # Lattice Control -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.LatticeControl.TestTransport

noncomputable section

/-! Explicit lattice conditions on a symplectic matrix imply scalar
action on every integral test with the specified period. -/

open scoped Classical _root_.Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

def FiniteLatticeControl (N : ℕ) (hN : 0 < N) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : Prop :=
  (∀ p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hN.ne')),
    PhaseAction.TestTransport.finiteMomentum g⁻¹ p 0 ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hN.ne')) ∧
    PhaseAction.TestTransport.finitePosition g⁻¹ p 0 ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne') ∧
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) (PhaseAction.TestTransport.finitePosition g⁻¹ p 0) ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne')) ∧
  (∀ q ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'),
    PhaseAction.TestTransport.finiteMomentum g⁻¹ 0 q ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hN.ne')) ∧
    PhaseAction.TestTransport.finitePosition g⁻¹ 0 q ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne') ∧
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) (PhaseAction.TestTransport.finiteMomentum g⁻¹ 0 q) ∈
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hN.ne'))) ∧
  (∀ a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors,
    PhaseAction.TestTransport.finiteMomentum g 0 a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors ∧
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) (PhaseAction.TestTransport.finiteMomentum g 0 a) ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors ∧
    PhaseAction.TestTransport.finitePosition g 0 a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors ∧
    PhaseAction.TestTransport.finitePosition g 0 a - a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'))

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)

theorem finite_lattice_control_scalar (N : ℕ) (hN : 0 < N) (m : MpF)
    (hm : FiniteLatticeControl N hN (D.finite.project m))
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (hperiod : ∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'), ∀ x,
      φ.val (u + x) = φ.val x) :
    ∃ c : ℂ, D.finite.action m φ = c • φ := by
  let r : ℚ := N
  have hr : r ≠ 0 := by
    change (N : ℚ) ≠ 0
    exact_mod_cast hN.ne'
  let f := RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction (ι := I) r hr
  let T := (D.finite.action m).toLinearMap
  have hmod (p : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hp : p ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r⁻¹ (inv_ne_zero hr)) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
      (T f).val x = D.finiteCharacter (∑ i, p i * x i) * (T f).val x := by
    obtain ⟨h1, h2, h3⟩ := hm.1 p hp
    have ht := PhaseAction.TestTransport.finite_intertwines_inverse_input D m p 0 f f (fun y =>
      (HeisenbergLattice.TestTransport.finite_heisenberg_lattice_fixed_half_translation D r hr _ _ h1 h2 h3 y).symm) x
    simpa only [T, LinearEquiv.coe_coe, RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization.finite_heisenberg_modulation] using ht
  have htrans (q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hq : q ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice r hr) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
      (T f).val (x - q) = (T f).val x := by
    obtain ⟨h1, h2, h3⟩ := hm.2.1 q hq
    have ht := PhaseAction.TestTransport.finite_intertwines_inverse_input D m 0 q f f (fun y =>
      (HeisenbergLattice.TestTransport.finite_heisenberg_lattice_fixed_half_modulation D r hr _ _ h1 h2 h3 y).symm) x
    simpa only [T, LinearEquiv.coe_coe, RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization.finite_heisenberg_translation] using ht.symm
  have hf : T f = (T f).val 0 • f :=
    BoundedScalar.TestTransport.finite_lattice_joint_eigenvector D r hr (T f) hmod htrans
  have hcoset (a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (ha : a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
      (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest r hr a)).val x = (T f).val (x - a) := by
    have ht := D.finite.intertwines m 0 a f (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest r hr a)
      (fun y => by rw [RepresentationTheory.Hecke.RadialDilation.FiniteHeisenberg.Realization.finite_heisenberg_translation]; rfl) x
    change (T (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest r hr a)).val x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter (PhaseAction.TestTransport.finiteMomentum (D.finite.project m) 0 a)
        (PhaseAction.TestTransport.finitePosition (D.finite.project m) 0 a) (T f).val x at ht
    rw [ht, hf]
    change _ * ((T f).val 0 * f.val _) = (T f).val 0 * f.val (x - a)
    rw [← mul_left_comm]
    congr 1
    obtain ⟨h1, h2, h3, h4⟩ := hm.2.2 a ha
    exact HeisenbergLattice.TestTransport.finite_heisenberg_integral_coset D r hr
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_nat_subset_integral N hN) _ _ a h1 h2 h3 h4 x
  exact ⟨(T f).val 0, BoundedScalar.TestTransport.finite_integral_periodic_operator_scalar D N hN T
    hmod htrans hcoset φ hsupport hperiod⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.LatticeControl.TestTransport
