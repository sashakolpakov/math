import OAI.AlgebraicGeometry.HilbertScheme.Presentations.VariableCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedCechExactness

/-! # Ordered Cech Reindexing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.OrderedCechReindexing.ProjectiveCech

noncomputable section

/-! Ordered bijections of variable sets identify actual projective Čech exactness. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type v} {τ : Type w}
variable (R : Type u) [CommRing R] (e : σ ↪ τ)
variable [Algebra (MvPolynomial τ R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)]
variable (he : ∀ i : σ, algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (X (e i)) = X i)

include he in
theorem retainedVariable_algebraMap_eq_kill (hsurj : Function.Surjective e) :
    algebraMap (MvPolynomial τ R) (MvPolynomial σ R) = (MvPolynomial.killCompl e.injective).toRingHom := by
  let φ := IsScalarTower.toAlgHom R (MvPolynomial τ R) (MvPolynomial σ R)
  have h : φ = MvPolynomial.killCompl e.injective := by
    apply MvPolynomial.algHom_ext
    intro j
    obtain ⟨i, rfl⟩ := hsurj j
    change algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (X (e i)) = MvPolynomial.killCompl e.injective (X (e i))
    rw [he i, ← MvPolynomial.rename_X e i, MvPolynomial.killCompl_rename_app]
  exact congrArg AlgHom.toRingHom h

variable [LinearOrder σ] [LinearOrder τ]
variable (M : Type t) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial τ R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial τ R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial τ R) (MvPolynomial σ R) M]

theorem ordered_moduleCechExactAt_iff (eOrd : σ ≃o τ)
    (heOrd : ∀ i : σ, algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (X (eOrd i)) = X i)
    (ℳ : ℤ → Submodule R M) (d : ℤ) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := τ) R M ℳ d q ↔ Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q :=
  EmbeddedCechExactness.ProjectiveCech.embedded_moduleCechExactAt_iff R eOrd.toOrderEmbedding
    (retainedVariable_algebraMap_eq_kill R eOrd.toEmbedding heOrd eOrd.surjective) M ℳ d q

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.OrderedCechReindexing.ProjectiveCech
