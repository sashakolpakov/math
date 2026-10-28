import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Immersion Complement Dimension -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionComplementDimension

noncomputable section

/-!
# The actual normal dimension of a finite-dimensional immersion

The complement occurring in an immersion's normal chart is finite dimensional,
and its dimension is forced by the source and target models. Consequently,
pointwise immersions in finite dimensions share one fixed normal model.
-/

open scoped _root_.Manifold ContDiff

variable {K E F M N : Type*} [RCLike K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup F] [NormedSpace K F] [FiniteDimensional K F]
variable [TopologicalSpace M] [ChartedSpace E M]
variable [TopologicalSpace N] [ChartedSpace F N]
variable {n : ℕ∞ω} {f : M → N} {x : M}

/-- The normal chart's actual complement injects linearly into its
finite-dimensional ambient model. -/
theorem immersionComplement_finiteDimensional
    (h : Manifold.IsImmersionAt 𝓘(K, E) 𝓘(K, F) n f x) :
    FiniteDimensional K h.complement := by
  apply FiniteDimensional.of_injective
    (h.equiv.toLinearEquiv.toLinearMap.comp (LinearMap.inr K E h.complement))
  exact h.equiv.injective.comp (Prod.mk_right_injective (0 : E))

variable [FiniteDimensional K E]

/-- The complement in genuine normal coordinates has precisely the expected
dimension; this is a consequence of its actual linear equivalence. -/
theorem immersionComplement_finrank
    (h : Manifold.IsImmersionAt 𝓘(K, E) 𝓘(K, F) n f x) :
    Module.finrank K h.complement = Module.finrank K F - Module.finrank K E := by
  let := immersionComplement_finiteDimensional h
  have hd := h.equiv.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at hd
  omega

/-- Identify the actual normal complement with a fixed coordinate space
whose dimension is the difference of target and source dimensions. -/
def immersionComplementEquivFin
    (h : Manifold.IsImmersionAt 𝓘(K, E) 𝓘(K, F) n f x) :
    h.complement ≃L[K] (Fin (Module.finrank K F - Module.finrank K E) → K) := by
  letI := immersionComplement_finiteDimensional h
  exact ContinuousLinearEquiv.ofFinrankEq (by
    rw [Module.finrank_fin_fun, immersionComplement_finrank h])

/-- Every pointwise immersion between the same finite-dimensional models
uses one common normal coordinate dimension. -/
theorem isImmersionOfComplement_of_forall_isImmersionAt
    (h : ∀ x, Manifold.IsImmersionAt 𝓘(K, E) 𝓘(K, F) n f x) :
    Manifold.IsImmersionOfComplement
      (Fin (Module.finrank K F - Module.finrank K E) → K)
      𝓘(K, E) 𝓘(K, F) n f := by
  intro x
  exact (h x).isImmersionAtOfComplement_complement.trans_F
    (immersionComplementEquivFin (h x))

/-- In finite-dimensional models, pointwise genuine normal forms assemble
to mathlib's global immersion predicate with its fixed complement. -/
theorem isImmersion_of_forall_isImmersionAt
    (h : ∀ x, Manifold.IsImmersionAt 𝓘(K, E) 𝓘(K, F) n f x) :
    Manifold.IsImmersion 𝓘(K, E) 𝓘(K, F) n f :=
  (isImmersionOfComplement_of_forall_isImmersionAt h).isImmersion

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionComplementDimension
