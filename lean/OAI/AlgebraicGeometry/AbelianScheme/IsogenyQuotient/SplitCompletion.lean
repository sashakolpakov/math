import OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Split Completion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitCompletion.Construction

noncomputable section

/-!
CMPoints's actual residue coordinates construct the split integral completion.
Surjectivity modulo q lifts by Nakayama; the equal finite free ranks then
give injectivity. No completion-isomorphism conclusion is assumed.
-/

open scoped TensorProduct

theorem padic_pi_surjective_of_residues
    (q : ℕ) [Fact q.Prime] {V I : Type*} [AddCommGroup V] [Module ℤ_[q] V] [Fintype I]
    (f : V →ₗ[ℤ_[q]] (I → ℤ_[q]))
    (hf : Function.Surjective (fun x i => PadicInt.toZModPow 1 (f x i))) :
    Function.Surjective f := by
  let J : Ideal ℤ_[q] := Ideal.span {(q : ℤ_[q])}
  apply f.surjective_of_surjective_comp_mkQ J
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, PadicInt.maximalIdeal_eq_span_p])
  intro z
  obtain ⟨y, rfl⟩ := (J • (⊤ : Submodule ℤ_[q] (I → ℤ_[q]))).mkQ_surjective z
  obtain ⟨x, hx⟩ := hf (fun i => PadicInt.toZModPow 1 (y i))
  refine ⟨x, (Submodule.Quotient.eq _).mpr ?_⟩
  have hd (i : I) : (q : ℤ_[q]) ∣ f x i - y i := by
    apply Ideal.mem_span_singleton.mp
    have hxi : PadicInt.toZModPow 1 (f x i) = PadicInt.toZModPow 1 (y i) := congrFun hx i
    have he : PadicInt.toZModPow 1 (f x i - y i) = 0 := by
      rw [map_sub, hxi, sub_self]
    have hm : f x i - y i ∈ RingHom.ker (PadicInt.toZModPow 1) := RingHom.mem_ker.mpr he
    simpa only [PadicInt.ker_toZModPow, pow_one] using hm
  choose c hc using hd
  have he : f x - y = (q : ℤ_[q]) • c := by
    funext i
    exact hc i
  rw [he]
  exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) Submodule.mem_top

variable {E L : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)

def l45CompletionMap :
    ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E →ₐ[ℤ_[q]] (Gal(E/ℚ) → ℤ_[q]) :=
  AlgHom.liftEquiv ℤ ℤ_[q] (NumberField.RingOfIntegers E) _
    (RingHom.pi (j.localCharacter iota)).toIntAlgHom

omit [IsGalois ℚ E] in
theorem l45CompletionMap_integer (a : NumberField.RingOfIntegers E) :
    l45CompletionMap j iota (1 ⊗ₜ[ℤ] a) = fun τ => j.localCharacter iota τ a := by
  change (1 : ℤ_[q]) • (fun τ => j.localCharacter iota τ a) = _
  exact one_smul _ _

omit [IsGalois ℚ E] in
include hsplit in
theorem l45CompletionMap_surjective : Function.Surjective (l45CompletionMap j iota) := by
  apply padic_pi_surjective_of_residues q (l45CompletionMap j iota).toLinearMap
  intro y
  obtain ⟨a, ha⟩ := (hsplit 1).1 y
  refine ⟨1 ⊗ₜ[ℤ] a, ?_⟩
  change (fun τ => PadicInt.toZModPow 1 (l45CompletionMap j iota (1 ⊗ₜ[ℤ] a) τ)) = y
  rw [l45CompletionMap_integer]
  exact ha

include hsplit in
theorem l45CompletionMap_bijective : Function.Bijective (l45CompletionMap j iota) := by
  let B := (NumberField.RingOfIntegers.basis E).baseChange ℤ_[q]
  have : Module.Free ℤ_[q] (ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) := Module.Free.of_basis B
  have : Module.Finite ℤ_[q] (ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) := Module.Finite.of_basis B
  have hr : Module.finrank ℤ_[q] (ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) =
      Module.finrank ℤ_[q] (Gal(E/ℚ) → ℤ_[q]) := by
    rw [Module.finrank_eq_card_basis B, Module.finrank_pi]
    calc
      _ = Module.finrank ℚ E := (Module.finrank_eq_card_basis (NumberField.integralBasis E)).symm
      _ = Fintype.card Gal(E/ℚ) := by rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  let e := LinearEquiv.ofFinrankEq (R := ℤ_[q])
    (ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) (Gal(E/ℚ) → ℤ_[q]) hr
  have hf := l45CompletionMap_surjective j iota hsplit
  have hi := Module.End.injective_of_surjective ℤ_[q] (Gal(E/ℚ) → ℤ_[q])
    (f := (l45CompletionMap j iota).toLinearMap.comp e.symm.toLinearMap)
    (hf.comp e.symm.surjective)
  refine ⟨fun x y hxy => e.injective (hi ?_), hf⟩
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    AlgHom.toLinearMap_apply] using hxy

def l45CompletionEquiv :
    ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E ≃ₐ[ℤ_[q]] (Gal(E/ℚ) → ℤ_[q]) :=
  AlgEquiv.ofBijective (l45CompletionMap j iota) (l45CompletionMap_bijective j iota hsplit)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitCompletion.Construction
