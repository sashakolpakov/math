import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Determinant
import Mathlib.NumberTheory.Padics.RingHoms

/-! # Cokernel Determinant -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CokernelDeterminant

noncomputable section

/-! The size of a finite cokernel over the p-adic integers is determined
by the valuation of the determinant. Smith normal form reduces the
statement to the actual residue quotients of the coefficient ring. -/

open _root_.Module

variable (p : ℕ) [Fact p.Prime]

theorem valuation_unit (u : ℤ_[p]ˣ) : (u : ℤ_[p]).valuation = 0 := by
  have h := PadicInt.valuation_mul (Units.ne_zero u) (Units.ne_zero u⁻¹)
  have hsum : 0 = (u : ℤ_[p]).valuation + (↑u⁻¹ : ℤ_[p]).valuation := by
    simpa only [← Units.val_mul, mul_inv_cancel, Units.val_one,
      PadicInt.valuation_one] using h
  omega

theorem valuation_eq_of_associated {a b : ℤ_[p]} (h : Associated a b) :
    a.valuation = b.valuation := by
  obtain ⟨u, rfl⟩ := h
  by_cases ha : a = 0
  · simp [ha]
  · rw [PadicInt.valuation_mul ha (Units.ne_zero u), valuation_unit, add_zero]

theorem scalar_quotient_card (a : ℤ_[p]) (ha : a ≠ 0) :
    Nat.card (ℤ_[p] ⧸ Ideal.span ({a} : Set ℤ_[p])) = p ^ a.valuation := by
  have hi : Ideal.span ({a} : Set ℤ_[p]) = Ideal.span {(p : ℤ_[p]) ^ a.valuation} := by
    calc
      Ideal.span ({a} : Set ℤ_[p]) =
          Ideal.span {(PadicInt.unitCoeff ha : ℤ_[p]) * (p : ℤ_[p]) ^ a.valuation} :=
        congrArg (fun x : ℤ_[p] => Ideal.span ({x} : Set ℤ_[p]))
          (PadicInt.unitCoeff_spec ha)
      _ = _ := Ideal.span_singleton_mul_left_unit (Units.isUnit _) _
  rw [hi, ← PadicInt.ker_toZModPow]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZModPow a.valuation))).toEquiv).trans
      (Nat.card_zmod _)

theorem valuation_prod {ι : Type*} (s : Finset ι) (a : ι → ℤ_[p])
    (ha : ∀ i ∈ s, a i ≠ 0) :
    (∏ i ∈ s, a i).valuation = ∑ i ∈ s, (a i).valuation := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      PadicInt.valuation_mul (ha i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => ha j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))]

variable {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
  [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M]

theorem quotient_card_of_equiv (N : Submodule ℤ_[p] M) (e : M ≃ₗ[ℤ_[p]] N) :
    Nat.card (M ⧸ N) = p ^ (N.subtype.comp e.toLinearMap).det.valuation := by
  classical
  let b := Module.Free.chooseBasis ℤ_[p] M
  have h : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  let e' : M ≃ₗ[ℤ_[p]] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[ℤ_[p]] M := N.subtype.comp e'.toLinearMap
  have heq : (N.subtype.comp e.toLinearMap).det.valuation = f.det.valuation :=
    valuation_eq_of_associated p (LinearMap.associated_det_comp_equiv N.subtype e e')
  rw [heq]
  have ha (i) : f (b' i) = a i • b' i := by
    change (b'.equiv ab (Equiv.refl _) (b' i) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact Submodule.smithNormalFormBotBasis_def b h i
  have hm : LinearMap.toMatrix b' b' f = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hd : f.det = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', hm, Matrix.det_diagonal]
  have han (i) : a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h i
  rw [hd, valuation_prod p _ _ (fun i _ => han i), ← Finset.prod_pow_eq_pow_sum]
  calc
    Nat.card (M ⧸ N) =
        Nat.card (∀ i, ℤ_[p] ⧸ Ideal.span ({a i} : Set ℤ_[p])) :=
      Nat.card_congr (N.quotientEquivPiSpan b h).toEquiv
    _ = ∏ i, p ^ (a i).valuation := by
      rw [Nat.card_pi]
      exact Finset.prod_congr rfl (fun i _ => scalar_quotient_card p (a i) (han i))

theorem cokernel_card (f : Module.End ℤ_[p] M) (hf : Function.Injective f) :
    Nat.card (M ⧸ f.range) = p ^ f.det.valuation :=
  quotient_card_of_equiv p f.range (LinearEquiv.ofInjective f hf)

theorem finite_cokernel (f : Module.End ℤ_[p] M) (hf : Function.Injective f) :
    Finite (M ⧸ f.range) := by
  apply (Nat.card_ne_zero.mp ?_).2
  rw [cokernel_card p f hf]
  exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CokernelDeterminant
