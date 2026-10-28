import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientComplex

/-! # Annihilated Parameter Complex -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AnnihilatedParameterComplex

noncomputable section

/-! Quotienting a complex by a scalar already annihilating every
term is an actual chain isomorphism, including its native homology. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Pointwise TensorProduct

universe u

variable (R : Type u) [CommRing R] (r : R)

theorem submodule_eq_bot (M : ModuleCat.{u} R) (hM : ∀ m : M, r • m = 0) :
    r • (⊤ : Submodule R M) = ⊥ := by
  apply le_antisymm _ bot_le
  intro m hm
  obtain ⟨n, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists m r (⊤ : Submodule R M)).mp hm
  exact hM n

theorem tensor (M N : ModuleCat.{u} R) (hM : ∀ m : M, r • m = 0) :
    ∀ t : M ⊗[R] N, r • t = 0 := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul m n => rw [TensorProduct.smul_tmul', hM m, TensorProduct.zero_tmul]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

theorem projection_isIso (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ i, ∀ m : K.X i, r • m = 0) :
    IsIso (Parameter.QuotientComplex.projection R r K) := by
  have h (i : ℕ) : IsIso ((Parameter.QuotientComplex.projection R r K).f i) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨?_, Submodule.mkQ_surjective _⟩
    apply LinearMap.ker_eq_bot.mp
    change (r • (⊤ : Submodule R (K.X i))).mkQ.ker = ⊥
    rw [Submodule.ker_mkQ]
    exact submodule_eq_bot R r (K.X i) (hK i)
  let := h
  exact HomologicalComplex.Hom.isIso_of_components _

theorem homology_length (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ i, ∀ m : K.X i, r • m = 0) (n : ℕ) :
    Module.length R ((Parameter.QuotientComplex.complex R r K).homology n) =
      Module.length R (K.homology n) := by
  let := projection_isIso R r K hK
  exact ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (asIso (Parameter.QuotientComplex.projection R r K))).toLinearEquiv.length_eq.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AnnihilatedParameterComplex
