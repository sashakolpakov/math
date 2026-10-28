import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Linear Normal Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.LinearNormalCoordinates.Algebra

noncomputable section

/-! A left inverse and a basis of normal covectors give joint linear coordinates. -/

open _root_.Algebra

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
  {n : ℕ}

theorem linearNormalCoordinates_bijective
    (L : V →ₗ[K] W) (R : W →ₗ[K] V) (hRL : R.comp L = LinearMap.id)
    (b : Module.Basis (Fin n) K (LinearMap.range L).dualAnnihilator) :
    Function.Bijective (R.prod (LinearMap.pi (fun i => (b i : Module.Dual K W)))) := by
  have hleft (v : V) : R (L v) = v := congrArg (fun T : V →ₗ[K] V => T v) hRL
  have hL : Function.Injective L := Function.LeftInverse.injective hleft
  let T := R.prod (LinearMap.pi (fun i => (b i : Module.Dual K W)))
  have hT : Function.Injective T := by
    apply (injective_iff_map_eq_zero T).mpr
    intro w hw
    have hRw : R w = 0 := congrArg Prod.fst hw
    have hbw (i : Fin n) : (b i : Module.Dual K W) w = 0 :=
      congrArg (fun p : V × (Fin n → K) => p.2 i) hw
    let E : (LinearMap.range L).dualAnnihilator →ₗ[K] K :=
      (Module.Dual.eval K W w).comp (LinearMap.range L).dualAnnihilator.subtype
    have hE : E = 0 := b.ext (fun i => hbw i)
    have hrange : w ∈ LinearMap.range L := by
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range L) w).mp
      intro φ hφ
      exact congrArg (fun F : (LinearMap.range L).dualAnnihilator →ₗ[K] K => F ⟨φ, hφ⟩) hE
    obtain ⟨v, rfl⟩ := hrange
    rw [hleft] at hRw
    rw [hRw, map_zero]
  have hdim : Module.finrank K W = Module.finrank K (V × (Fin n → K)) := by
    have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range L)
    rw [LinearMap.finrank_range_of_inj hL, Module.finrank_eq_card_basis b, Fintype.card_fin] at hd
    rw [Module.finrank_prod, Module.finrank_fin_fun]
    exact hd.symm
  exact ⟨hT, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hT⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.LinearNormalCoordinates.Algebra
