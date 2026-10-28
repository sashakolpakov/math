import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Wedge

/-! # Higher Smooth Symbols -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HigherSmoothSymbols

noncomputable section

/-!
# Higher-degree realization by actual exterior products

The symbol a₀ da₁ ∧ ⋯ ∧ daₙ is constructed using smooth zero-forms,
their actual exterior derivatives, and the standard exterior product.
The differential identity is proved in every degree.
-/

open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {A : Type*} [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a : A, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))

def smoothSymbol : (n : ℕ) → (Fin (n + 1) → A) → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n
  | 0, a => Smooth.FormRealization.zeroFormMap φ hφ (a 0)
  | n + 1, a => AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (smoothSymbol n (Fin.init a))
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Smooth.FormRealization.zeroFormMap φ hφ (a (Fin.last (n + 1)))))

@[simp]
theorem smoothSymbol_zero (a : Fin 1 → A) :
    HigherSmoothSymbols.smoothSymbol φ hφ 0 a = Smooth.FormRealization.zeroFormMap φ hφ (a 0) := rfl

@[simp]
theorem smoothSymbol_succ (n : ℕ) (a : Fin (n + 2) → A) :
    HigherSmoothSymbols.smoothSymbol φ hφ (n + 1) a =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (HigherSmoothSymbols.smoothSymbol φ hφ n (Fin.init a))
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Smooth.FormRealization.zeroFormMap φ hφ (a (Fin.last (n + 1))))) := rfl

omit [CommRing A] [Algebra ℂ A] in
theorem init_cons {n : ℕ} (c : A) (a : Fin (n + 1) → A) :
    Fin.init (Fin.cons c a : Fin (n + 2) → A) =
      (Fin.cons c (Fin.init a) : Fin (n + 1) → A) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change (Fin.cons c a : Fin (n + 2) → A) j.succ.castSucc = a j.castSucc
    rw [← Fin.succ_castSucc, Fin.cons_succ]

/-- The ordinary exterior derivative realizes formal algebraic differentiation. -/
theorem smoothSymbol_d : ∀ (n : ℕ) (a : Fin (n + 1) → A),
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (HigherSmoothSymbols.smoothSymbol φ hφ n a) =
      HigherSmoothSymbols.smoothSymbol φ hφ (n + 1) (Fin.cons 1 a) := by
  intro n
  induction n with
  | zero =>
      intro a
      change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Smooth.FormRealization.zeroFormMap φ hφ (a 0)) =
        AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (Smooth.FormRealization.zeroFormMap φ hφ 1) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Smooth.FormRealization.zeroFormMap φ hφ (a 0)))
      exact (Smooth.Wedge.manifoldWedge_unit_zero_one φ hφ _).symm
  | succ n ih =>
      intro a
      rw [smoothSymbol_succ, Smooth.Wedge.manifoldWedge_d_exact, ih, Smooth.Wedge.manifoldDegreeCast_refl]
      conv_rhs => rw [smoothSymbol_succ, init_cons, Fin.cons_last]

/-- Complex-linear realization before descending the algebraic relations. -/
def rawSmoothMap (n : ℕ) : Algebraic.Forms.RawForm A n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n :=
  Finsupp.linearCombination ℂ (HigherSmoothSymbols.smoothSymbol φ hφ n)

@[simp]
theorem rawSmoothMap_symbol (n : ℕ) (a : Fin (n + 1) → A) :
    rawSmoothMap φ hφ n (Algebraic.Forms.symbol A a) = HigherSmoothSymbols.smoothSymbol φ hφ n a := by
  simp [rawSmoothMap, Algebraic.Forms.symbol]

/-- The raw realization commutes with both actual differentials in every degree. -/
theorem rawSmoothMap_d (n : ℕ) (r : Algebraic.Forms.RawForm A n) :
    rawSmoothMap φ hφ (n + 1) (Algebraic.Forms.rawDifferential A n r) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (rawSmoothMap φ hφ n r) := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s ihr ihs => simp only [map_add, ihr, ihs]
  | single a c =>
      have hc : Finsupp.single a c = c • Algebraic.Forms.symbol A a := by
        simp [Algebraic.Forms.symbol]
      rw [hc]
      simp only [map_smul, Algebraic.Forms.rawDifferential_symbol, rawSmoothMap_symbol,
        smoothSymbol_d]

end

end OAI.AlgebraicGeometry.Comparison.Betti.HigherSmoothSymbols
