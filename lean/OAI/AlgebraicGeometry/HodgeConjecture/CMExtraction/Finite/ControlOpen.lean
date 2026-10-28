import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.LatticeControl
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.SymplecticTopology

/-! # Control Open -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.ControlOpen.TestTransport

noncomputable section

/-! The explicit lattice control conditions form a neighborhood of
the identity in the finite symplectic group. -/

open scoped Classical _root_.Matrix _root_.Topology
open _root_.Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]
  (N : ℕ) (hN : 0 < N)

theorem finiteLatticeControl_one : LatticeControl.TestTransport.FiniteLatticeControl (I := I) N hN 1 := by
  have hp (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : PhaseAction.TestTransport.finiteMomentum 1 p q = p := by
    change (fun i => ((1 : Matrix (I ⊕ I) (I ⊕ I) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) *ᵥ Sum.elim p q) (Sum.inl i)) = p
    rw [Matrix.one_mulVec]
    rfl
  have hq (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : PhaseAction.TestTransport.finitePosition 1 p q = q := by
    change (fun i => ((1 : Matrix (I ⊕ I) (I ⊕ I) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) *ᵥ Sum.elim p q) (Sum.inr i)) = q
    rw [Matrix.one_mulVec]
    rfl
  have hzero : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) (0 : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) = 0 := by
    ext i
    simp only [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale, Pi.zero_apply, mul_zero]
  constructor
  · intro p h
    simpa only [inv_one, hp, hq, hzero] using
      And.intro h (And.intro (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne')).zero_mem
        (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne')).zero_mem)
  constructor
  · intro q h
    simpa only [inv_one, hp, hq, hzero] using
      And.intro (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hN.ne'))).zero_mem
        (And.intro h (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hN.ne'))).zero_mem)
  · intro a h
    simpa only [hp, hq, hzero, sub_self] using
      And.intro RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem (And.intro RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem
        (And.intro h (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne')).zero_mem))

theorem finiteLatticeControl_isOpen : IsOpen {g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | LatticeControl.TestTransport.FiniteLatticeControl N hN g} := by
  let L := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) (N : ℚ) (by exact_mod_cast hN.ne')
  let M := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) (N : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hN.ne'))
  have hL : IsOpen (L : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isOpen _ _
  have hM : IsOpen (M : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isOpen _ _
  have hLc : IsCompact (L : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isCompact _ _
  have hMc : IsCompact (M : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isCompact _ _
  have hmod : IsOpen {g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | ∀ p ∈ M,
      PhaseAction.TestTransport.finiteMomentum g⁻¹ p 0 ∈ M ∧ PhaseAction.TestTransport.finitePosition g⁻¹ p 0 ∈ L ∧
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) (PhaseAction.TestTransport.finitePosition g⁻¹ p 0) ∈ L} := by
    apply CompactPrincipalLevel.Approximation.compact_forall_mem_open
      (fun z : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) =>
        (PhaseAction.TestTransport.finiteMomentum z.1⁻¹ z.2 0, PhaseAction.TestTransport.finitePosition z.1⁻¹ z.2 0))
      _ _ hMc {z : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) |
        z.1 ∈ M ∧ z.2 ∈ L ∧ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) z.2 ∈ L}
    · exact (hM.preimage continuous_fst).inter ((hL.preimage continuous_snd).inter
        (hL.preimage ((RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous (1 / 2)).comp continuous_snd)))
    · fun_prop
  have htrans : IsOpen {g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | ∀ q ∈ L,
      PhaseAction.TestTransport.finiteMomentum g⁻¹ 0 q ∈ M ∧ PhaseAction.TestTransport.finitePosition g⁻¹ 0 q ∈ L ∧
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) (PhaseAction.TestTransport.finiteMomentum g⁻¹ 0 q) ∈ M} := by
    apply CompactPrincipalLevel.Approximation.compact_forall_mem_open
      (fun z : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) =>
        (PhaseAction.TestTransport.finiteMomentum z.1⁻¹ 0 z.2, PhaseAction.TestTransport.finitePosition z.1⁻¹ 0 z.2))
      _ _ hLc {z : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) |
        z.1 ∈ M ∧ z.2 ∈ L ∧ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) z.1 ∈ M}
    · exact (hM.preimage continuous_fst).inter ((hL.preimage continuous_snd).inter
        (hM.preimage ((RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous (1 / 2)).comp continuous_fst)))
    · fun_prop
  have hcos : IsOpen {g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf | ∀ a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors,
      PhaseAction.TestTransport.finiteMomentum g 0 a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors ∧
      RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) (PhaseAction.TestTransport.finiteMomentum g 0 a) ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors ∧
      PhaseAction.TestTransport.finitePosition g 0 a ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors ∧ PhaseAction.TestTransport.finitePosition g 0 a - a ∈ L} := by
    apply CompactPrincipalLevel.Approximation.compact_forall_mem_open
      (fun z : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) =>
        (PhaseAction.TestTransport.finiteMomentum z.1 0 z.2, PhaseAction.TestTransport.finitePosition z.1 0 z.2, PhaseAction.TestTransport.finitePosition z.1 0 z.2 - z.2))
      _ _ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isCompact {z : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) |
        z.1 ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors ∧ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (1 / 2) z.1 ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors ∧
        z.2.1 ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors ∧ z.2.2 ∈ L}
    · exact (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isOpen.preimage continuous_fst).inter
        ((RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isOpen.preimage ((RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous (1 / 2)).comp continuous_fst)).inter
        ((RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isOpen.preimage (continuous_fst.comp continuous_snd)).inter
        (hL.preimage (continuous_snd.comp continuous_snd))))
    · fun_prop
  exact hmod.inter (htrans.inter hcos)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.ControlOpen.TestTransport
