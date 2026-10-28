import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.VariableRegularity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.SequenceBasic
import Mathlib.Data.List.Nodup

/-! # Variable Sequence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.VariableSequence

noncomputable section

/-! A list of distinct polynomial variables is a regular sequence. This supplies actual regular parameters before localization, over every nonzero coefficient ring. -/
universe u v
variable {R : Type u} [CommRing R] {ι : Type v}

theorem variable_list_ideal (xs : List ι) :
    Regular.SequenceBasic.Ideal.ofList (xs.map (MvPolynomial.X : ι → MvPolynomial ι R)) =
      Ideal.span (MvPolynomial.X '' {i | i ∈ xs}) := by
  apply congrArg Ideal.span
  ext p
  exact List.mem_map

theorem variable_list_weakly_regular (xs : List ι) (hxs : xs.Nodup) :
    Regular.SequenceBasic.RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (xs.map (MvPolynomial.X : ι → MvPolynomial ι R)) := by
  classical
  constructor
  intro i hi
  have hi' : i < xs.length := by simpa only [List.length_map] using hi
  have hfresh : xs[i] ∉ {j | j ∈ xs.take i} := by
    intro hmem
    obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hmem
    have hki : k < i := by
      simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi')] using hk
    have hk' : k < xs.length := lt_trans hki hi'
    have heq' : xs[k] = xs[i] := by simpa only [List.getElem_take] using heq
    exact (Nat.ne_of_lt hki) (hxs.getElem_inj_iff.mp heq')
  rw [List.getElem_map, ← List.map_take, variable_list_ideal, Ideal.smul_eq_mul, Ideal.mul_top]
  exact VariableRegularity.fresh_variable_smul_regular_quotient (R := R) {j | j ∈ xs.take i} xs[i] hfresh

theorem variable_list_regular [Nontrivial R] (xs : List ι) (hxs : xs.Nodup) :
    Regular.SequenceBasic.RingTheory.Sequence.IsRegular (MvPolynomial ι R) (xs.map (MvPolynomial.X : ι → MvPolynomial ι R)) := by
  refine ⟨variable_list_weakly_regular xs hxs, ?_⟩
  rw [Ideal.smul_eq_mul, Ideal.mul_top, variable_list_ideal]
  intro htop
  have hle : Ideal.span (MvPolynomial.X '' {i | i ∈ xs}) ≤
      RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : ι => 0)) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, _, rfl⟩
    simp
  have hone : (1 : MvPolynomial ι R) ∈
      RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : ι => 0)) :=
    hle (htop ▸ (show (1 : MvPolynomial ι R) ∈ (⊤ : Ideal (MvPolynomial ι R)) from trivial))
  simp at hone

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.VariableSequence
