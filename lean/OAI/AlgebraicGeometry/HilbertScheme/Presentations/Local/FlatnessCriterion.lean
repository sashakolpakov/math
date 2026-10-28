import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AdicIdealTensorFlatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Presentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorNilpotentDevissage
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Flatness Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatnessCriterion

noncomputable section

/-! The Noetherian local criterion for flatness, proved from the actual
maximal-ideal tensor multiplication kernel. -/

open TensorProduct

universe u v w
variable {B : Type u} [CommRing B]

theorem ideal_quotient_annihilated_of_le (I J : Ideal B) (h : I ≤ J) :
    I • (⊤ : Submodule B (B ⧸ J)) = ⊥ := by
  apply bot_unique
  apply Submodule.smul_le.mpr
  intro r hr x _
  apply (Submodule.mem_bot B).mpr
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk J (r * a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (J.mul_mem_right a (h hr))

theorem flatPresentation_idealTensor_injective_of_maximalIdeal_test
    {F : Type w} [AddCommGroup F] [Module B F] [Module.Flat B F]
    {M : Type v} [AddCommGroup M] [Module B M]
    (q : F →ₗ[B] M) (hq : Function.Surjective q)
    (m : Ideal B) [m.IsMaximal]
    (hm : Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M m))
    (I : Ideal B) (n : ℕ) (hn : m ^ n ≤ I) :
    Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M I) := by
  have hmk : Function.Injective (q.ker.subtype.lTensor (B ⧸ m)) :=
    (IdealTensor.Presentation.presentation_tensor_quotient_injective_iff q hq m).mpr hm
  have hnk : Function.Injective (q.ker.subtype.lTensor (B ⧸ I)) :=
    TensorNilpotentDevissage.lTensor_injective_of_maximalIdeal_power (B := B) (K := q.ker) (F := F)
      q.ker.subtype m hmk n (B ⧸ I) (ideal_quotient_annihilated_of_le (m ^ n) I hn)
  exact (IdealTensor.Presentation.presentation_tensor_quotient_injective_iff q hq I).mp hnk

theorem idealTensor_injective_of_maximalIdeal_test
    (M : Type v) [AddCommGroup M] [Module B M]
    (m : Ideal B) [m.IsMaximal]
    (hm : Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M m))
    (I : Ideal B) (n : ℕ) (hn : m ^ n ≤ I) :
    Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M I) := by
  let F := M →₀ B
  let q : F →ₗ[B] M := Finsupp.linearCombination B id
  have hq : Function.Surjective q := Finsupp.linearCombination_id_surjective B M
  exact flatPresentation_idealTensor_injective_of_maximalIdeal_test q hq m hm I n hn

theorem flat_of_maximalIdeal_tensor_injective
    [IsNoetherianRing B] [IsLocalRing B]
    (S : Type w) [CommRing S] [Algebra B S] [IsNoetherianRing S] [IsLocalRing S]
    [IsLocalHom (algebraMap B S)]
    (M : Type v) [AddCommGroup M] [Module B M] [Module S M] [IsScalarTower B S M]
    [Module.Finite S M]
    (hm : Function.Injective
      (IdealTensor.Obstruction.idealTensorMultiplication B B M (IsLocalRing.maximalIdeal B))) :
    Module.Flat B M := by
  have hmap : (IsLocalRing.maximalIdeal B).map (algebraMap B S) ≤
      IsLocalRing.maximalIdeal S := IsLocalRing.map_maximalIdeal_le (algebraMap B S)
  have hjac : IsLocalRing.maximalIdeal S ≤ Ideal.jacobson (⊥ : Ideal S) :=
    IsLocalRing.maximalIdeal_le_jacobson _
  apply AdicIdealTensorFlatness.flat_of_adic_idealTensor_injective M S (IsLocalRing.maximalIdeal B) (hmap.trans hjac)
  intro I n
  exact idealTensor_injective_of_maximalIdeal_test M (IsLocalRing.maximalIdeal B) hm
    (I ⊔ IsLocalRing.maximalIdeal B ^ n) n le_sup_right

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatnessCriterion
