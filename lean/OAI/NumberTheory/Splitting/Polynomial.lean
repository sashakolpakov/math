import Mathlib

/-! # Polynomial -/

namespace OAI.NumberTheory.Splitting.Polynomial.SplitPrimesConstruction

open _root_.Polynomial

/-- Chinese remainders for a monic polynomial with distinct roots in the base field. -/
theorem quotient_equiv_fun_of_splits_separable
    {K : Type*} [Field K] (f : K[X]) (hm : f.Monic)
    (hs : f.Splits) (hsep : f.Separable) :
    Nonempty ((K[X] ⧸ Ideal.span {f}) ≃+* (Fin f.natDegree → K)) := by
  classical
  have hn : f.roots.Nodup := nodup_roots hsep
  let r : Finset K := ⟨f.roots, hn⟩
  have hr : Fintype.card r = f.natDegree := by
    simpa [r] using hs.natDegree_eq_card_roots.symm
  let v : r → K[X] := fun x ↦ X - C (x : K)
  have hv : ∀ i j : r, i ≠ j → IsCoprime (v i) (v j) := by
    intro i j hij
    exact isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr (fun h ↦ hij (Subtype.ext h))).isUnit
  have hprod : (∏ i : r, v i) = f := by
    change (∏ i : r, (X - C (i : K))) = f
    rw [Finset.prod_coe_sort r (fun x : K ↦ (X - C x : K[X]))]
    simpa [r, Finset.prod_mk] using (hs.eq_prod_roots_of_monic hm).symm
  have hi : (⨅ i : r, Ideal.span {v i}) = Ideal.span {f} := by
    rw [Ideal.iInf_span_singleton hv, hprod]
  let e := (Ideal.quotEquivOfEq hi.symm).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i : r ↦ Ideal.span {v i})
      (fun i j hij ↦ (Ideal.isCoprime_span_singleton_iff _ _).mpr (hv i j hij)))
  let e' : (∀ i : r, K[X] ⧸ Ideal.span {v i}) ≃+* (r → K) :=
    RingEquiv.piCongrRight fun i ↦ (quotientSpanXSubCAlgEquiv (i : K)).toRingEquiv
  exact ⟨e.trans (e'.trans (RingEquiv.piCongrLeft' (fun _ : r ↦ K)
    ((Fintype.equivFin r).trans (finCongr hr)) ))⟩

/-- Separability in characteristic zero survives reduction away from a
single nonzero integer, obtained from a resultant Bezout identity. -/
theorem exists_separability_denominator
    (f : ℤ[X]) (hf : f.natDegree ≠ 0)
    (hsep : (f.map (Int.castRingHom ℚ)).Separable) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ d →
      (f.map (Int.castRingHom (ZMod p))).Separable := by
  let d := f.resultant f.derivative f.natDegree f.derivative.natDegree
  have hd : d ≠ 0 := by
    intro hd
    have h := resultant_ne_zero (f.map (Int.castRingHom ℚ))
      ((f.derivative).map (Int.castRingHom ℚ))
      (by simpa [separable_def, derivative_map] using hsep)
    apply h
    rw [natDegree_map_eq_of_injective (Int.cast_injective),
      natDegree_map_eq_of_injective (Int.cast_injective), resultant_map_map]
    change (d : ℚ) = 0
    simp [hd]
  obtain ⟨a, b, _, _, hab⟩ := exists_mul_add_mul_eq_C_resultant
    f f.derivative le_rfl le_rfl (by omega)
  refine ⟨d, hd, ?_⟩
  intro p hp hpd
  have : Fact p.Prime := ⟨hp⟩
  have hd' : (d : ZMod p) ≠ 0 := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hpd
  have hab' := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) hab
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hab'
  refine ⟨C (d : ZMod p)⁻¹ * a.map (Int.castRingHom (ZMod p)),
    C (d : ZMod p)⁻¹ * b.map (Int.castRingHom (ZMod p)), ?_⟩
  rw [derivative_map]
  calc
    _ = C (d : ZMod p)⁻¹ *
        ((f.map (Int.castRingHom (ZMod p))) * a.map (Int.castRingHom (ZMod p)) +
          f.derivative.map (Int.castRingHom (ZMod p)) * b.map (Int.castRingHom (ZMod p))) := by ring
    _ = C (d : ZMod p)⁻¹ * C (d : ZMod p) := by rw [hab']; rfl
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hd', C_1]

end OAI.NumberTheory.Splitting.Polynomial.SplitPrimesConstruction
