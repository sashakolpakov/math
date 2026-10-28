import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.RealOperators
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators

/-! # Product Operators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ProductOperators.CM

noncomputable section

/-! The actual real and finite extensions commute and give a genuine
product action on the adelic Schwartz space. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators.CM.Sections
variable {I : Type*} [Fintype I]

theorem commute (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I)
    (V : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    Commute (RealOperators.CM.operator U) (FiniteOperators.CM.operator V) := by
  apply LinearEquiv.toLinearMap_injective
  apply FiniteOperators.CM.Sections.linear_ext
  intro f φ
  change RealOperators.CM.operator U (FiniteOperators.CM.operator V (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ)) =
    FiniteOperators.CM.operator V (RealOperators.CM.operator U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ))
  rw [RealOperators.CM.operator_tensor, FiniteOperators.CM.operator_tensor,
    RealOperators.CM.operator_tensor, FiniteOperators.CM.operator_tensor]

def operator : ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) ×
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)) →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) where
  toFun a := RealOperators.CM.operator a.1 * FiniteOperators.CM.operator a.2
  map_one' := by rw [Prod.fst_one, Prod.snd_one, map_one, map_one, mul_one]
  map_mul' a b := by
    change RealOperators.CM.operator (a.1 * b.1) *
      FiniteOperators.CM.operator (a.2 * b.2) = _
    rw [map_mul, map_mul]
    exact (commute b.1 a.2).mul_mul_mul_comm _ _

theorem operator_tensor (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I)
    (V : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : operator (U, V) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (U f) (V φ) := by
  change RealOperators.CM.operator U (FiniteOperators.CM.operator V (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ)) = _
  rw [FiniteOperators.CM.operator_tensor, RealOperators.CM.operator_tensor]

theorem real_neg : RealOperators.CM.operator (LinearEquiv.neg ℂ (M := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I)) =
    LinearEquiv.neg ℂ := by
  apply LinearEquiv.toLinearMap_injective
  apply FiniteOperators.CM.Sections.linear_ext
  intro f φ
  change RealOperators.CM.operator (LinearEquiv.neg ℂ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = -(RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ)
  rw [RealOperators.CM.operator_tensor]
  apply Subtype.ext
  funext x
  exact neg_mul _ _

theorem finite_neg : FiniteOperators.CM.operator (LinearEquiv.neg ℂ (M := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)) =
    LinearEquiv.neg ℂ := by
  apply LinearEquiv.toLinearMap_injective
  apply FiniteOperators.CM.Sections.linear_ext
  intro f φ
  change FiniteOperators.CM.operator (LinearEquiv.neg ℂ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = -(RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ)
  rw [FiniteOperators.CM.operator_tensor]
  apply Subtype.ext
  funext x
  exact mul_neg _ _

theorem neg_neg : operator ((LinearEquiv.neg ℂ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I),
    (LinearEquiv.neg ℂ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)) = 1 := by
  change RealOperators.CM.operator (LinearEquiv.neg ℂ) *
    FiniteOperators.CM.operator (LinearEquiv.neg ℂ) = 1
  rw [real_neg, finite_neg]
  apply LinearEquiv.ext
  intro f
  exact _root_.neg_neg f

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ProductOperators.CM
