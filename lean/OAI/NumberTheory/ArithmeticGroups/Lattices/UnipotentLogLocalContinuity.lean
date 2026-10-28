import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.UnipotentExponentialEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.LocalModelInverseContinuity

/-! # Unipotent Log Local Continuity -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The unique positive logarithm is continuous on a neighborhood
of the identity, by comparison with the ambient local operator logarithm. -/

open scoped Classical _root_.Topology
open Filter NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance UnipotentLogLocalContinuity.Construction.positiveLogEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance UnipotentLogLocalContinuity.Construction.positiveLogEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance UnipotentLogLocalContinuity.Construction.positiveLogEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance UnipotentLogLocalContinuity.Construction.positiveLog_complete : CompleteSpace L := FiniteDimensional.complete ℝ L

theorem KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentExpEquiv_zero
    (d : KillingSplit.Construction.KillingSplitWeightData B) : d.positiveUnipotentExpEquiv 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact exp_zero

theorem KillingSplit.Construction.KillingSplitWeightData.positiveLog_eventually_continuousAt
    (d : KillingSplit.Construction.KillingSplitWeightData B) :
    ∀ᶠ g in 𝓝 (1 : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)),
      ContinuousAt d.positiveUnipotentExpEquiv.symm g := by
  let E := DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val
  let G := UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)
  let W := Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)
  let e := d.positiveUnipotentExpEquiv
  let I := ContinuousLinearEquiv.refl ℝ (L →L[ℝ] L)
  have hd : HasStrictFDerivAt exp I.toContinuousLinearMap 0 := hasStrictFDerivAt_exp_zero
  let p := hd.toOpenPartialHomeomorph exp
  let U : Set E := {X | X.val ∈ p.source}
  have hU : U ∈ 𝓝 0 :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (p.open_source.mem_nhds hd.mem_toOpenPartialHomeomorph_source)
  let j : G → (L →L[ℝ] L) := fun g => g.val.val
  have hj : Continuous j := Units.continuous_val.comp continuous_subtype_val
  let Z : G → W := fun g => ⟨j g - 1, g.property.2⟩
  have hZ : Continuous Z := (hj.sub continuous_const).subtype_mk _
  have hZ₁ : Z 1 = 0 := by
    apply Subtype.ext
    exact sub_self 1
  have hlocalW := UnipotentLocalExponential.Construction.unipotent_bracket_local_exponential_within B d.basis d.regularElement.val
    (d.le_symmetric d.regularElement.property) (fun i => d.weight i d.regularElement)
    (fun i => d.eigenvector i d.regularElement) U hU
  have hZlim : Tendsto Z (𝓝 1) (𝓝 0) := hZ₁ ▸ hZ.continuousAt.tendsto
  have hlocal : ∀ᶠ g in 𝓝 (1 : G), ∃ X : E, X.val ∈ p.source ∧ e X = g := by
    filter_upwards [hZlim.eventually hlocalW] with g hg
    have hZeq : 1 + (Z g).val = j g := by
      change 1 + (j g - 1) = j g
      abel
    have hgB : ∀ x y, (1 + (Z g).val) (B x y) = B ((1 + (Z g).val) x) ((1 + (Z g).val) y) := by
      rw [hZeq]
      exact g.property.1
    obtain ⟨X, hX, hXe⟩ := hg hgB
    refine ⟨X, hX, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact hXe.trans hZeq
  have he0 : e 0 = 1 := d.positiveUnipotentExpEquiv_zero
  have h := LocalModelInverseContinuity.Construction.continuous_inverse_eventually_of_local_model e (fun X : E => X.val)
    Topology.IsEmbedding.subtypeVal j hj p 0 (fun _ => rfl) (he0.symm ▸ hlocal)
  simpa only [he0] using h

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
