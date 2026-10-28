import OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic

/-! # Completion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Completion.CM

noncomputable section

/-! The integral local decomposition is derived from CMPoints's actual
split residue coordinates. Nakayama lifts surjectivity modulo q to the
completion, and the equality of integral ranks gives injectivity. -/

open scoped Classical TensorProduct
open TensorProduct _root_.NumberField

variable {q : ℕ} [Fact q.Prime]

/-- A map to a finite free q-adic module is surjective if its reduction
modulo q is surjective. -/
theorem surjective_of_residue_coordinates
    {M I : Type*} [AddCommGroup M] [Module ℤ_[q] M] [Fintype I]
    (f : M →ₗ[ℤ_[q]] (I → ℤ_[q]))
    (hres : ∀ y : I → ZMod (q ^ 1),
      ∃ x : M, ∀ i, PadicInt.toZModPow 1 (f x i) = y i) :
    Function.Surjective f := by
  let J : Ideal ℤ_[q] := IsLocalRing.maximalIdeal ℤ_[q]
  have hJ : J ≤ (⊥ : Ideal ℤ_[q]).jacobson :=
    (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
  apply LinearMap.range_eq_top.mp
  apply top_le_iff.mp
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ
  intro y _
  obtain ⟨x, hx⟩ := hres (fun i => PadicInt.toZModPow 1 (y i))
  have hdiff : y - f x ∈ J • (⊤ : Submodule ℤ_[q] (I → ℤ_[q])) := by
    rw [← (Pi.basisFun ℤ_[q] I).sum_repr (y - f x)]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem_smul _ (Submodule.mem_top)
    change y i - f x i ∈ IsLocalRing.maximalIdeal ℤ_[q]
    rw [PadicInt.maximalIdeal_eq_span_p]
    have hz : y i - f x i ∈ RingHom.ker (PadicInt.toZModPow (p := q) 1) := by
      change PadicInt.toZModPow 1 (y i - f x i) = 0
      rw [map_sub, hx i, sub_self]
    simpa only [PadicInt.ker_toZModPow, pow_one] using hz
  have hxmem : f x ∈ LinearMap.range f ⊔ J • ⊤ :=
    Submodule.mem_sup_left ⟨x, rfl⟩
  have hsum := (LinearMap.range f ⊔ J • ⊤).add_mem hxmem
    (Submodule.mem_sup_right hdiff)
  simpa only [add_sub_cancel] using hsum

variable {E K : Type} [Field E] [NumberField E]
  [IsGalois ℚ E] [Field K] [NumberField K] {κ : K →+* ℂ}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)

/-- Extension of the actual integral local characters to the integral
q-adic tensor product. -/
def completionLinear :
    ℤ_[q] ⊗[ℤ] RingOfIntegers E →ₗ[ℤ_[q]] (Gal(E/ℚ) → ℤ_[q]) :=
  AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf ℤ_[q] ℤ_[q] _).symm
    (RingHom.pi (j.localCharacter iota)).toIntAlgHom.toLinearMap)

omit [IsGalois ℚ E] in
@[simp] theorem completionLinear_tmul (a : ℤ_[q]) (x : RingOfIntegers E) (τ : Gal(E/ℚ)) :
    completionLinear j iota (a ⊗ₜ[ℤ] x) τ = a * j.localCharacter iota τ x := rfl

/-- CMPoints's split coordinates imply the literal product decomposition
of the integral completion, with the same embedding labels. -/
theorem completion_bijective (hsplit : j.HasSplitCoordinates iota) :
    Function.Bijective (completionLinear j iota) := by
  have hs : Function.Surjective (completionLinear j iota) := by
    apply surjective_of_residue_coordinates
    intro y
    obtain ⟨x, hx⟩ := (hsplit 1).1 y
    exact ⟨1 ⊗ₜ[ℤ] x, fun τ => by
      simpa only [completionLinear_tmul, one_mul,
        PELModuli.CMPoints.Arithmetic.QadicChoice.residueCoordinates,
        PELModuli.CMPoints.Arithmetic.QadicChoice.residueCharacter, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk, RingHom.comp_apply] using congrFun hx τ⟩
  have hdim : Module.finrank ℤ_[q] (Gal(E/ℚ) → ℤ_[q]) =
      Module.finrank ℤ_[q] (ℤ_[q] ⊗[ℤ] RingOfIntegers E) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_baseChange,
      RingOfIntegers.rank, ← IsGalois.card_aut_eq_finrank ℚ E,
      Nat.card_eq_fintype_card]
  let e := LinearEquiv.ofFinrankEq
    (R := ℤ_[q]) (Gal(E/ℚ) → ℤ_[q]) (ℤ_[q] ⊗[ℤ] RingOfIntegers E) hdim
  have hinj : Function.Injective ((completionLinear j iota).comp e.toLinearMap) :=
    Module.End.injective_of_surjective ℤ_[q] (Gal(E/ℚ) → ℤ_[q])
    (hs.comp e.surjective)
  refine ⟨?_, hs⟩
  intro x y hxy
  apply e.symm.injective
  apply hinj
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using hxy

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Completion.CM
