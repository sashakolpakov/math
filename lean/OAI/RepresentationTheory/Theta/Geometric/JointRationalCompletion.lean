import OAI.RepresentationTheory.Theta.Geometric.JointLocalLattice
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalCompletion
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Joint Rational Completion -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original local embeddings identify the full rational completion
of E cubed with all of its split coordinates simultaneously. -/

open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.localEmbedding_eq_rationalLocalCharacter (hc : D.HasFiniteCoordinates) (v : Fin s × Bool) :
    D.localEmbedding v = (D.pel.rationalLocalCharacter v).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := NumberField.RingOfIntegers E)
  intro a
  exact (hc.1 v a).trans (D.pel.rationalLocalCharacter_integer v a).symm

def Data.ActiveHeckeThetaData.localCoordinateSwap : (Fin 3 → Fin s × Bool → ℚ_[q]) ≃ₗ[ℚ_[q]]
    (Fin s × Bool → Fin 3 → ℚ_[q]) where
  toFun u v i := u i v
  invFun u i v := u v i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Data.ActiveHeckeThetaData.jointRationalCompletion (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) :
    (ℚ_[q] ⊗[ℚ] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) ≃ₗ[ℚ_[q]] (Fin s × Bool → Fin 3 → ℚ_[q]) :=
  (TensorProduct.piRight ℚ ℚ_[q] ℚ_[q] (fun _ : Fin 3 => E)).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin 3 =>
      (D.pel.rationalCompletionEquiv hgood hdegree).toLinearEquiv)).trans Data.ActiveHeckeThetaData.localCoordinateSwap)

theorem Data.ActiveHeckeThetaData.jointRationalCompletion_tmul (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (hc : D.HasFiniteCoordinates)
    (a : ℚ_[q]) (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    D.jointRationalCompletion hgood hdegree (a ⊗ₜ[ℚ] x) = a • D.jointLocalEmbedding x := by
  funext v i
  change a * D.pel.rationalLocalCharacter v (x i) = a * D.localEmbedding v (x i)
  rw [D.localEmbedding_eq_rationalLocalCharacter hc]
  rfl

theorem Data.ActiveHeckeThetaData.jointRationalCompletion_one_tmul (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (hc : D.HasFiniteCoordinates) (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    D.jointRationalCompletion hgood hdegree (1 ⊗ₜ[ℚ] x) = D.jointLocalEmbedding x := by
  rw [D.jointRationalCompletion_tmul hgood hdegree hc, one_smul]

end

end OAI.RepresentationTheory.Theta.Geometric
