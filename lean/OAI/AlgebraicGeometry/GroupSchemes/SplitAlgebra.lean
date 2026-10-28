import OAI.AlgebraicGeometry.GroupSchemes.FiniteAlgebra

/-! # Split Algebra -/

namespace OAI.AlgebraicGeometry.GroupSchemes.SplitAlgebra.FiniteEtale

noncomputable section

/-! Enough distinct rational points split a finite algebra. -/

universe u v

variable (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
variable {ι : Type v} [Fintype ι]

/-- Evaluation at a family of k-points. -/
def evaluation (f : ι → A →ₐ[k] k) : A →ₐ[k] (ι → k) := AlgHom.pi f

/-- As many distinct points as the dimension separate all elements of the algebra. -/
theorem evaluation_injective (f : ι → A →ₐ[k] k) (hf : Function.Injective f)
    (hdim : Fintype.card ι = Module.finrank k A) :
    Function.Injective (evaluation k A f) := by
  have hlin := (linearIndependent_algHom_toLinearMap k A k).comp f hf
  have hspan := hlin.span_eq_top_of_card_eq_finrank' (by
    simpa only [Subspace.dual_finrank_eq] using hdim)
  change Submodule.span k (Set.range (fun i => (f i).toLinearMap)) = ⊤ at hspan
  apply (injective_iff_map_eq_zero (evaluation k A f).toLinearMap).mpr
  intro x hx
  apply (Module.forall_dual_apply_eq_zero_iff k x).mp
  intro φ
  have hφ : φ ∈ Submodule.span k (Set.range (fun i => (f i).toLinearMap)) := by
    rw [hspan]
    trivial
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨i, rfl⟩ := hφ
    exact congrFun hx i
  | zero => rfl
  | add φ ψ _ _ hφ hψ => simp only [LinearMap.add_apply, hφ, hψ, add_zero]
  | smul c φ _ hφ => simp only [LinearMap.smul_apply, hφ, smul_zero]

/-- Evaluation is an algebra isomorphism when the distinct-point count equals the dimension. -/
def evaluationEquiv (f : ι → A →ₐ[k] k) (hf : Function.Injective f)
    (hdim : Fintype.card ι = Module.finrank k A) : A ≃ₐ[k] (ι → k) :=
  AlgEquiv.ofBijective (evaluation k A f)
    ⟨evaluation_injective k A f hf hdim,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (evaluation k A f).toLinearMap) (by simpa using hdim.symm)).mp
        (evaluation_injective k A f hf hdim)⟩

omit [Fintype ι] [Module.Finite k A] in
/-- Rational points separate elements of a split finite algebra. -/
theorem eq_of_points [Algebra.IsFiniteSplit k A] {x y : A}
    (h : ∀ f : A →ₐ[k] k, f x = f y) : x = y := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun k A
  apply e.injective
  funext i
  exact h ((Pi.evalAlgHom k (fun _ : Fin n => k) i).comp e.toAlgHom)

end

end OAI.AlgebraicGeometry.GroupSchemes.SplitAlgebra.FiniteEtale
