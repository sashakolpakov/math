import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientParameters
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Quotient Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.QuotientParameters

noncomputable section

/-!
A finite product of the constructed Grassmannians parametrizes degree
quotients through a specified bound. Its affine points are exactly tuples
of actual fixed-rank homogeneous-module quotients.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable (σ : Type v) [Finite σ] (B : ℕ) (r : ℕ → ℕ)

def truncatedQuotientParameters (S : Scheme.{max u v}) : Over S :=
  ∏ᶜ (fun d : Fin (B + 1) => Homogeneous.QuotientParameters.homogeneousQuotientParameterScheme.{u, v} σ d (r d) S)

def truncatedQuotientProjection (S : Scheme.{max u v}) (d : Fin (B + 1)) :
    truncatedQuotientParameters.{u, v} σ B r S ⟶
      Homogeneous.QuotientParameters.homogeneousQuotientParameterScheme.{u, v} σ d (r d) S :=
  Pi.π _ d

def truncatedQuotientTupleMap {S : Scheme.{max u v}} {T : Over S}
    (q : ∀ d : Fin (B + 1), T ⟶ Homogeneous.QuotientParameters.homogeneousQuotientParameterScheme.{u, v} σ d (r d) S) :
    T ⟶ truncatedQuotientParameters.{u, v} σ B r S :=
  Pi.lift q

omit [Finite σ] in
theorem truncatedQuotientTupleMap_projection {S : Scheme.{max u v}} {T : Over S}
    (q : ∀ d : Fin (B + 1), T ⟶ Homogeneous.QuotientParameters.homogeneousQuotientParameterScheme.{u, v} σ d (r d) S)
    (d : Fin (B + 1)) :
    truncatedQuotientTupleMap σ B r q ≫ truncatedQuotientProjection σ B r S d = q d :=
  Pi.lift_comp_π q d

def truncatedQuotientAffinePointEquiv {S : Scheme.{max u v}}
    (A : CommRingCat.{max u v}) (f : Spec A ⟶ S) :
    (∀ d : Fin (B + 1), Module.Grassmannian A
      (MvPolynomial.homogeneousSubmodule σ A d) (r d)) ≃
        (Over.mk f ⟶ truncatedQuotientParameters.{u, v} σ B r S) where
  toFun Q := truncatedQuotientTupleMap σ B r
    (fun d => Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d (r d) A f (Q d))
  invFun x d := (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d (r d) A f).symm
    (x ≫ truncatedQuotientProjection σ B r S d)
  left_inv Q := by
    funext d
    dsimp only
    rw [truncatedQuotientTupleMap_projection, Equiv.symm_apply_apply]
  right_inv x := by
    apply Pi.hom_ext
    intro d
    change truncatedQuotientTupleMap σ B r _ ≫ truncatedQuotientProjection σ B r S d = _
    rw [truncatedQuotientTupleMap_projection, Equiv.apply_symm_apply]
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.QuotientParameters
