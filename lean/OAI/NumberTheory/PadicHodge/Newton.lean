import OAI.NumberTheory.PadicHodge.Valuation

/-! # Newton -/

namespace OAI.NumberTheory.PadicHodge.Newton.CM.ExtremeSlopesAdapter

noncomputable section

/-! The determinant valuation of a coefficient summand follows from its
Frobenius slopes, including the restriction-of-scalars degree factor. -/

open scoped TensorProduct

variable (q : ℕ) [Fact q.Prime]

lemma valuation_multiset_prod_of_constant
    (s : Multiset (AlgebraicClosure ℚ_[q])) (r : ℚ)
    (hs : ∀ x ∈ s, x ≠ 0 ∧ Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q x = r) :
    Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q s.prod = (s.card : ℚ) * r := by
  induction s using Multiset.induction_on with
  | empty => simpa using Valuation.CM.ExtremeSlopesAdapter.algebraicValuation_algebraMap q 1
  | @cons x s ih =>
    have hx := hs x (Multiset.mem_cons_self x s)
    have hs' : ∀ y ∈ s, y ≠ 0 ∧ Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q y = r :=
      fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    rw [Multiset.prod_cons,
      Valuation.CM.ExtremeSlopesAdapter.algebraicValuation_mul q x s.prod hx.1
        (Multiset.prod_ne_zero (fun hz => (hs' 0 hz).1 rfl)),
      hx.2, ih hs', Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- The determinant valuation is the sum of Frobenius slopes, with multiplicity. -/
theorem valuation_det_of_constant_slope
    {V : Type*} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[q]) V]
    [FiniteDimensional (AlgebraicClosure ℚ_[q]) V]
    (φ : Module.End (AlgebraicClosure ℚ_[q]) V) (r : ℚ)
    (hslopes : ∀ x, φ.HasEigenvalue x →
      Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation q x = (r : WithTop ℚ)) :
    Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q φ.det =
      (Module.finrank (AlgebraicClosure ℚ_[q]) V : ℚ) * r := by
  have hs := IsAlgClosed.splits φ.charpoly
  rw [Module.End.det_eq_prod_roots_charpoly_of_splits hs]
  have hroot : ∀ x ∈ φ.charpoly.roots,
      x ≠ 0 ∧ Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q x = r := by
    intro x hx
    have he : φ.HasEigenvalue x :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly φ x).mpr
        ((Polynomial.mem_roots φ.charpoly_monic.ne_zero).mp hx)
    have hv := hslopes x he
    have hx0 : x ≠ 0 := (Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation q).ne_top_iff.mp (by rw [hv]; simp)
    refine ⟨hx0, ?_⟩
    rw [Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation_apply q x hx0] at hv
    exact WithTop.coe_inj.mp hv
  rw [valuation_multiset_prod_of_constant q _ r hroot,
    ← hs.natDegree_eq_card_roots, φ.charpoly_natDegree]

/-- The rational Newton number used in GeometricComparison has the required coefficient
multiplicity. No semisimplicity of Frobenius is assumed. -/
theorem rational_newton_of_constant_slope
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Module ℚ_[q] V] [IsScalarTower ℚ_[q] L V]
    (φ : V ≃ₗ[L] V) (r : ℚ)
    (hslopes : ∀ x, Module.End.HasEigenvalue (φ.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) x →
      Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation q x = (r : WithTop ℚ)) :
    (Padic.valuation (p := q) (LinearMap.det (φ.restrictScalars ℚ_[q]).toLinearMap) : ℚ) =
      (Module.finrank ℚ_[q] L : ℚ) * (Module.finrank L V : ℚ) * r := by
  have hdet : φ.toLinearMap.det ≠ 0 := by
    simpa only [LinearEquiv.coe_det] using Units.ne_zero (LinearEquiv.det φ)
  change (Padic.valuation (p := q) (LinearMap.det (φ.toLinearMap.restrictScalars ℚ_[q])) : ℚ) = _
  rw [LinearMap.det_restrictScalars, Valuation.CM.ExtremeSlopesAdapter.valuation_norm q L.val _ hdet]
  have h := valuation_det_of_constant_slope q
    (φ.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) r hslopes
  rw [LinearMap.det_baseChange, Module.finrank_baseChange] at h
  rw [show Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (L.val φ.toLinearMap.det) =
    (Module.finrank L V : ℚ) * r from h]
  ring

end

end OAI.NumberTheory.PadicHodge.Newton.CM.ExtremeSlopesAdapter
