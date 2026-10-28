import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitCompletion
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Rational Split Completion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RationalSplitCompletion.Construction

noncomputable section

/-!
The rational split completion uses the same actual field embeddings as
the integral one. The comparison on integral tensors supplies every
coordinate vector, proving surjectivity and hence the rational isomorphism.
-/

open scoped TensorProduct

variable {E L : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)

def l45FieldCharacter (τ : Gal(E/ℚ)) : E →+* ℚ_[q] :=
  (j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime)).comp
    (iota.comp τ.toRingHom)

omit [IsGalois ℚ E] in
theorem l45FieldCharacter_integer (τ : Gal(E/ℚ)) (a : NumberField.RingOfIntegers E) :
    l45FieldCharacter j iota τ (a : E) = (j.localCharacter iota τ a : ℚ_[q]) :=
  (RingHom.congr_fun j.integral_compatibility
    (NumberField.RingOfIntegers.mapRingHom (iota.comp τ.toRingHom) a)).symm

def l45RationalCompletionMap :
    ℚ_[q] ⊗[ℚ] E →ₐ[ℚ_[q]] (Gal(E/ℚ) → ℚ_[q]) :=
  AlgHom.liftEquiv ℚ ℚ_[q] E _ (RingHom.pi (l45FieldCharacter j iota)).toRatAlgHom

omit [IsGalois ℚ E] in
theorem l45RationalCompletionMap_integer (a : E) :
    l45RationalCompletionMap j iota (1 ⊗ₜ[ℚ] a) = fun τ => l45FieldCharacter j iota τ a := by
  change (1 : ℚ_[q]) • (fun τ => l45FieldCharacter j iota τ a) = _
  exact one_smul _ _

def integralToRationalCompletion :
    ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E →ₗ[ℤ_[q]] ℚ_[q] ⊗[ℚ] E :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : ℤ_[q] →ₗ[ℤ_[q]] ℤ_[q]).smulRight
      (((TensorProduct.mk ℚ ℚ_[q] E 1).restrictScalars ℤ).comp
        (algebraMap (NumberField.RingOfIntegers E) E).toIntAlgHom.toLinearMap))

omit [IsGalois ℚ E] in
theorem l45CompletionMap_rational_comparison
    (z : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) (τ : Gal(E/ℚ)) :
    l45RationalCompletionMap j iota (integralToRationalCompletion (E := E) (q := q) z) τ =
      (SplitCompletion.Construction.l45CompletionMap j iota z τ : ℚ_[q]) := by
  induction z using TensorProduct.inductionOn with
  | tmul a r =>
    change l45RationalCompletionMap j iota ((a : ℚ_[q]) • (1 ⊗ₜ[ℚ] (r : E))) τ =
      ((a * j.localCharacter iota τ r : ℤ_[q]) : ℚ_[q])
    rw [map_smul, l45RationalCompletionMap_integer]
    simp only [Pi.smul_apply, smul_eq_mul, l45FieldCharacter_integer, PadicInt.coe_mul]
  | add z w hz hw =>
    simp only [map_add, Pi.add_apply, PadicInt.coe_add, hz, hw]

omit [IsGalois ℚ E] in
include hsplit in
theorem l45RationalCompletionMap_surjective : Function.Surjective (l45RationalCompletionMap j iota) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← (Pi.basisFun ℚ_[q] Gal(E/ℚ)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨τ, rfl⟩
  obtain ⟨z, hz⟩ := SplitCompletion.Construction.l45CompletionMap_surjective j iota hsplit (Pi.single τ 1)
  refine ⟨integralToRationalCompletion (E := E) (q := q) z, ?_⟩
  ext υ
  change l45RationalCompletionMap j iota (integralToRationalCompletion z) υ = _
  rw [l45CompletionMap_rational_comparison, hz]
  by_cases h : τ = υ
  · subst υ
    simp
  · simp [h]

include hsplit in
theorem l45RationalCompletionMap_bijective : Function.Bijective (l45RationalCompletionMap j iota) := by
  let B := (NumberField.integralBasis E).baseChange ℚ_[q]
  have hr : Module.finrank ℚ_[q] (ℚ_[q] ⊗[ℚ] E) =
      Module.finrank ℚ_[q] (Gal(E/ℚ) → ℚ_[q]) := by
    rw [Module.finrank_eq_card_basis B, Module.finrank_pi]
    calc
      _ = Module.finrank ℚ E := (Module.finrank_eq_card_basis (NumberField.integralBasis E)).symm
      _ = Fintype.card Gal(E/ℚ) := by rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  let e := LinearEquiv.ofFinrankEq (R := ℚ_[q]) (ℚ_[q] ⊗[ℚ] E) (Gal(E/ℚ) → ℚ_[q]) hr
  have hf := l45RationalCompletionMap_surjective j iota hsplit
  have hi := Module.End.injective_of_surjective ℚ_[q] (Gal(E/ℚ) → ℚ_[q])
    (f := (l45RationalCompletionMap j iota).toLinearMap.comp e.symm.toLinearMap)
    (hf.comp e.symm.surjective)
  refine ⟨fun x y hxy => e.injective (hi ?_), hf⟩
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    AlgHom.toLinearMap_apply] using hxy

def l45RationalCompletionEquiv : ℚ_[q] ⊗[ℚ] E ≃ₐ[ℚ_[q]] (Gal(E/ℚ) → ℚ_[q]) :=
  AlgEquiv.ofBijective (l45RationalCompletionMap j iota) (l45RationalCompletionMap_bijective j iota hsplit)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RationalSplitCompletion.Construction
