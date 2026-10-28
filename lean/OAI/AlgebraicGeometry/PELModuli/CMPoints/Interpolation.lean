import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic

/-! # Interpolation -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Interpolation

noncomputable section

/-! Chinese remainders interpolate arbitrary tuples of q-adic characters
modulo q^n once those characters are distinct modulo q. -/

open _root_.Polynomial Function

theorem polynomial_evaluation_surjective_of_unit_differences
    {R Idx : Type*} [CommRing R] [Fintype Idx]
    (v : Idx → R) (hv : ∀ i j, i ≠ j → IsUnit (v i - v j)) :
    Function.Surjective (fun p : R[X] => fun i => p.eval (v i)) := by
  intro u
  let I (i : Idx) : Ideal R[X] := Ideal.span {X - C (v i)}
  have hI : Pairwise (IsCoprime on I) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (hv i j hij))
  obtain ⟨p, hp⟩ := Ideal.exists_forall_sub_mem_ideal hI (fun i => C (u i))
  refine ⟨p, funext fun i => ?_⟩
  have h := Polynomial.dvd_iff_isRoot.mp (Ideal.mem_span_singleton.mp (hp i))
  simpa only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero] using h

theorem padic_unit_of_nonzero_residue {q : ℕ} [Fact q.Prime]
    (a : PadicInt q) (ha : PadicInt.toZMod a ≠ 0) : IsUnit a := by
  apply PadicInt.isUnit_iff.mpr
  exact le_antisymm (PadicInt.norm_le_one a)
    (le_of_not_gt fun h => ha ((LocalPadic.toZMod_eq_zero_iff_norm_lt_one a).mpr h))

/-- Surjectivity at every q-power follows from separation at the first level. -/
theorem characters_surjective_mod_pow
    {A Idx : Type*} [CommRing A] [Fintype Idx]
    {q : ℕ} [Fact q.Prime] (χ : Idx → A →+* PadicInt q) (θ : A)
    (hχ : Function.Injective (fun i => PadicInt.toZMod (χ i θ))) (n : ℕ) :
    Function.Surjective (fun a : A => fun i => PadicInt.toZModPow n (χ i a)) := by
  intro u
  let v (i : Idx) : ZMod (q ^ n) := PadicInt.toZModPow n (χ i θ)
  have hv (i j : Idx) (hij : i ≠ j) : IsUnit (v i - v j) := by
    have hne : PadicInt.toZMod (χ i θ - χ j θ) ≠ 0 := by
      rw [map_sub, sub_ne_zero]
      exact fun h => hij (hχ h)
    simpa only [map_sub] using (padic_unit_of_nonzero_residue _ hne).map (PadicInt.toZModPow n)
  obtain ⟨p, hp⟩ := polynomial_evaluation_surjective_of_unit_differences v hv u
  obtain ⟨P, hP⟩ := Polynomial.map_surjective
    (f := Int.castRingHom (ZMod (q ^ n))) ZMod.intCast_surjective p
  refine ⟨P.aeval θ, funext fun i => ?_⟩
  have he : ((PadicInt.toZModPow n).comp (χ i)) (P.aeval θ) =
      (P.map (Int.castRingHom (ZMod (q ^ n)))).eval (v i) := by
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval_map]
    congr 1
    ext z
    simp
  rw [hP] at he
  exact he.trans (congrFun hp i)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Interpolation
