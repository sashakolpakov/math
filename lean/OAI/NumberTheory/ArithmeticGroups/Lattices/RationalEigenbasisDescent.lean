import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.Annihilator
import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization

/-! # Rational Eigenbasis Descent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RationalEigenbasisDescent.Construction

noncomputable section

/-! An eigenbasis whose eigenvalues are rational descends to the original
characteristic-zero field, even when the original eigenvectors do not. -/

open scoped Classical

theorem matrix_has_eigenbasis_of_eigenspaces_span
    {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (hspan : (⨆ a : k, Module.End.eigenspace (Matrix.toLin' A) a) = ⊤) :
    ∃ (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → k),
      ∀ i, Matrix.toLin' A (b i) = w i • b i := by
  let f : Module.End k (Fin n → k) := Matrix.toLin' A
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.eigenspaces_iSupIndep hspan
  let I := (a : k) × Fin (Module.finrank k (f.eigenspace a))
  let b : Module.Basis I k (Fin n → k) :=
    eigenDecomp.collectedBasis fun a => Module.finBasis k (f.eigenspace a)
  let : Fintype I := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card I = Fintype.card (Fin n) := by
    simpa using (Module.finrank_eq_card_basis b).symm
  let e : I ≃ Fin n := Fintype.equivOfCardEq hcard
  refine ⟨b.reindex e, fun i => (e.symm i).1, fun i => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact Module.End.mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ (e.symm i))

theorem aeval_eq_zero_of_eigenbasis
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V) (f : Module.End k V) (w : ι → k)
    (hf : ∀ i, f (b i) = w i • b i) (p : Polynomial k) (hp : ∀ i, p.eval (w i) = 0) :
    Polynomial.aeval f p = 0 := by
  apply b.ext
  intro i
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hf i), hp i, zero_smul, LinearMap.zero_apply]

theorem rational_eigenbasis_from_annihilator
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (s : Finset ℚ)
    (hf : Polynomial.aeval (Matrix.toLin' A)
      (∏ q ∈ s, (Polynomial.X - Polynomial.C (q : k))) = 0) :
    ∃ (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → ℚ),
      ∀ i, Matrix.toLin' A (b i) = (w i : k) • b i := by
  let p : Polynomial k := ∏ q ∈ s, (Polynomial.X - Polynomial.C (q : k))
  have hprod : (∏ a ∈ s.image (fun q : ℚ => (q : k)), (Polynomial.X - Polynomial.C a)) = p := by
    rw [Finset.prod_image]
    intro a _ b _ h
    exact Rat.cast_injective h
  have hspan : (⨆ a : k, Module.End.eigenspace (Matrix.toLin' A) a) = ⊤ := by
    apply Split.Annihilator.Construction.eigenspaces_span_of_split_annihilator _ (s.image fun q : ℚ => (q : k))
    rwa [hprod]
  obtain ⟨b, w, hb⟩ := matrix_has_eigenbasis_of_eigenspaces_span A hspan
  have hw (i : Fin n) : ∃ q : ℚ, (q : k) = w i := by
    have hz := LinearMap.congr_fun hf (b i)
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hb i), LinearMap.zero_apply] at hz
    have hzero : p.eval (w i) = 0 := (smul_eq_zero.mp hz).resolve_right (b.ne_zero i)
    simp only [p, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hzero
    obtain ⟨q, _, hq⟩ := Finset.prod_eq_zero_iff.mp hzero
    exact ⟨q, (sub_eq_zero.mp hq).symm⟩
  choose v hv using hw
  exact ⟨b, v, fun i => by rw [hv i]; exact hb i⟩

theorem rational_eigenbasis_descends
    {k K : Type} [Field k] [CharZero k] [Field K] [CharZero K] [Algebra k K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k)
    (b : Module.Basis (Fin n) K (Fin n → K)) (w : Fin n → ℚ)
    (hb : ∀ i, Matrix.toLin' (A.map (algebraMap k K)) (b i) = (w i : K) • b i) :
    ∃ (b₀ : Module.Basis (Fin n) k (Fin n → k)) (w₀ : Fin n → ℚ),
      ∀ i, Matrix.toLin' A (b₀ i) = (w₀ i : k) • b₀ i := by
  let s := Finset.univ.image w
  let p : Polynomial k := ∏ q ∈ s, (Polynomial.X - Polynomial.C (q : k))
  have he : Polynomial.aeval (Matrix.toLin' (A.map (algebraMap k K)))
      (p.map (algebraMap k K)) = 0 := by
    apply aeval_eq_zero_of_eigenbasis b _ (fun i => (w i : K)) hb
    intro i
    simp only [p, Polynomial.map_prod, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    simp
  have hm : Polynomial.aeval (A.map (algebraMap k K)) (p.map (algebraMap k K)) = 0 := by
    apply Matrix.toLinAlgEquiv'.injective
    rw [← Polynomial.aeval_algHom_apply, map_zero]
    exact he
  have hk : Polynomial.aeval A p = 0 := by
    rw [← SemisimpleMatrixDiagonalization.Construction.matrix_aeval_map] at hm
    ext i j : 1
    apply (algebraMap k K).injective
    simpa only [Matrix.map_apply, Matrix.zero_apply, map_zero] using congrFun (congrFun hm i) j
  apply rational_eigenbasis_from_annihilator A s
  change Polynomial.aeval (Matrix.toLinAlgEquiv' A) p = 0
  rw [Polynomial.aeval_algHom_apply, hk, map_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RationalEigenbasisDescent.Construction
