import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.HeisenbergLattice

/-! # Phase Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction.TestTransport

noncomputable section

/-! The actual symplectic action on momentum and position coordinates. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

def finiteMomentum (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i => (g.val *ᵥ Sum.elim p q) (Sum.inl i)

def finitePosition (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i => (g.val *ᵥ Sum.elim p q) (Sum.inr i)

theorem finitePhase_elim (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Sum.elim (finiteMomentum g p q) (finitePosition g p q) = g.val *ᵥ Sum.elim p q := by
  funext i
  cases i <;> rfl

theorem finiteMomentum_cancel (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    finiteMomentum g (finiteMomentum g⁻¹ p q) (finitePosition g⁻¹ p q) = p := by
  change (fun i => (g.val *ᵥ Sum.elim (finiteMomentum g⁻¹ p q)
    (finitePosition g⁻¹ p q)) (Sum.inl i)) = p
  rw [finitePhase_elim, Matrix.mulVec_mulVec]
  have h : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  rw [h, Matrix.one_mulVec]
  rfl

theorem finitePosition_cancel (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    finitePosition g (finiteMomentum g⁻¹ p q) (finitePosition g⁻¹ p q) = q := by
  change (fun i => (g.val *ᵥ Sum.elim (finiteMomentum g⁻¹ p q)
    (finitePosition g⁻¹ p q)) (Sum.inr i)) = q
  rw [finitePhase_elim, Matrix.mulVec_mulVec]
  have h : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  rw [h, Matrix.one_mulVec]
  rfl

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)

theorem finite_intertwines_inverse_input (m : MpF) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (hh : ∀ x, h.val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter
      (finiteMomentum (D.finite.project m)⁻¹ p q)
      (finitePosition (D.finite.project m)⁻¹ p q) f.val x) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finite.action m h).val x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter p q (D.finite.action m f).val x := by
  have ht := D.finite.intertwines m _ _ f h hh x
  change (D.finite.action m h).val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter
    (finiteMomentum (D.finite.project m)
      (finiteMomentum (D.finite.project m)⁻¹ p q) (finitePosition (D.finite.project m)⁻¹ p q))
    (finitePosition (D.finite.project m)
      (finiteMomentum (D.finite.project m)⁻¹ p q) (finitePosition (D.finite.project m)⁻¹ p q))
    (D.finite.action m f).val x at ht
  simpa only [finiteMomentum_cancel, finitePosition_cancel] using ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction.TestTransport
