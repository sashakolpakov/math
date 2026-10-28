import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.IncidenceLifting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedParameters

/-! # Graded Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Finite tuples of actual homogeneous quotients satisfying multiplication
compatibility have unique maps to the constructed closed parameter scheme.
These classifying maps distinguish the quotient tuples.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

structure Truncated.GradedClassification.TruncatedGradedQuotientData (R : Type u) [CommRing R] (σ : Type v)
    (B : ℕ) (r : ℕ → ℕ) where
  quotient : ∀ d : Fin (B + 1),
    Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R d) (r d)
  variable_mul : ∀ (d : Fin B) (i : σ), (quotient d.castSucc).toSubmodule ≤
    ((quotient d.succ).toSubmodule).comap (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i)

theorem Truncated.GradedClassification.TruncatedGradedQuotientData.ext {R : Type u} [CommRing R] {σ : Type v}
    {B : ℕ} {r : ℕ → ℕ} {D E : Truncated.GradedClassification.TruncatedGradedQuotientData R σ B r}
    (h : D.quotient = E.quotient) : D = E := by
  cases D
  cases E
  cases h
  rfl

def GradedQuotientFamilies.GradedQuotientData.truncate {R : Type u} [CommRing R] {σ : Type v} {r : ℕ → ℕ}
    (D : GradedQuotientFamilies.GradedQuotientData R σ r) (B : ℕ) : Truncated.GradedClassification.TruncatedGradedQuotientData R σ B r where
  quotient d := D.quotient d
  variable_mul d i := D.variable_mul d i

namespace Truncated.GradedClassification.TruncatedGradedQuotientData

variable {σ : Type v} [Finite σ] {B : ℕ} {r : ℕ → ℕ}
variable {R : CommRingCat.{max u v}} {S : Scheme.{max u v}}
variable (D : TruncatedGradedQuotientData R σ B r) (f : Spec R ⟶ S)

theorem existsUnique_classifyingMap :
    ∃! g : Over.mk f ⟶ GradedParameters.truncatedGradedParameters.{u, v} σ B r S,
      ∀ d : Fin (B + 1), g ≫ GradedParameters.truncatedGradedProjection σ B r S d =
        Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d (r d) R f (D.quotient d) := by
  let q := fun d : Fin (B + 1) =>
    Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d (r d) R f (D.quotient d)
  apply (GradedParameters.truncatedGradedParameters_universal σ B r S q).mp
  intro a
  exact Homogeneous.IncidenceLifting.homogeneousIncidenceCondition_of_affine_relations σ a.1 (r a.1) (r a.1.succ)
    (QuotientParameters.truncatedQuotientProjection σ B r S a.1.castSucc)
    (QuotientParameters.truncatedQuotientProjection σ B r S a.1.succ) R f
    (QuotientParameters.truncatedQuotientTupleMap σ B r q) (D.quotient a.1.castSucc) (D.quotient a.1.succ)
    (QuotientParameters.truncatedQuotientTupleMap_projection σ B r q a.1.castSucc)
    (QuotientParameters.truncatedQuotientTupleMap_projection σ B r q a.1.succ) a.2 (D.variable_mul a.1 a.2)

def classifyingMap : Over.mk f ⟶ GradedParameters.truncatedGradedParameters.{u, v} σ B r S :=
  (D.existsUnique_classifyingMap f).choose

theorem classifyingMap_projection (d : Fin (B + 1)) :
    D.classifyingMap f ≫ GradedParameters.truncatedGradedProjection σ B r S d =
      Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d (r d) R f (D.quotient d) :=
  (D.existsUnique_classifyingMap f).choose_spec.1 d

theorem classifyingMap_injective :
    Function.Injective (fun D : TruncatedGradedQuotientData R σ B r => D.classifyingMap f) := by
  intro D E h
  apply ext
  funext d
  apply (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d (r d) R f).injective
  exact (D.classifyingMap_projection f d).symm.trans
    ((congrArg (fun g => g ≫ GradedParameters.truncatedGradedProjection σ B r S d) h).trans
      (E.classifyingMap_projection f d))

end Truncated.GradedClassification.TruncatedGradedQuotientData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
