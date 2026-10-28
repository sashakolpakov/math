import OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentProductHomeomorphism
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingSplitFlowInverse
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingExponential

/-! # Raising Product Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingProductCoordinates.Construction

noncomputable section

/-! Split-invariant complementary subspaces give global product
coordinates on the ambient positive unipotent operators. -/

open NormedSpace Filter
open scoped _root_.Topology

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

local instance weightProductEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance weightProductEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance weightProductEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance weightProduct_complete : CompleteSpace L := FiniteDimensional.complete ℝ L

theorem weightRaising_exists_exponential_product_homeomorph
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (U V : Submodule ℝ (Positive.DerivationNilpotence.Construction.weightRaisingOperators b w)) (hUV : IsCompl U V)
    (hU : ∀ t x, x ∈ U → RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig t x ∈ U)
    (hV : ∀ t x, x ∈ V → RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig t x ∈ V) :
    ∃ e : U × V ≃ₜ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w,
      ∀ p, (e p).val = exp p.1.val.val * exp p.2.val.val - 1 := by
  apply NilpotentProductHomeomorphism.Construction.exists_exponential_product_homeomorph (Positive.DerivationNilpotence.Construction.weightRaisingOperators b w)
    (fun x hx y hy => RaisingMultiplication.Construction.weightRaisingOperators_mul b w x y hx hy)
    (fun x hx => RaisingExponential.Construction.weightRaising_exp_sub_one_mem b w x hx) U V hUV
    (fun t => (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv ((-t) • H)).conjContinuousAlgEquiv)
    (RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig) (fun _ _ => rfl) hU _ hV _ atTop
    (RaisingSplitFlow.Construction.weightRaisingSplitFlow_contracts b H hH w heig)
  · intro t x hx
    rw [RaisingSplitFlowInverse.Construction.weightRaisingSplitFlow_symm_apply]
    exact hU (-t) x hx
  · intro t x hx
    rw [RaisingSplitFlowInverse.Construction.weightRaisingSplitFlow_symm_apply]
    exact hV (-t) x hx

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingProductCoordinates.Construction
