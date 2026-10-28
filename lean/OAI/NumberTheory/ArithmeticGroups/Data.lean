import Mathlib
import OAI.Geometry.ComplexBall.PrescribedSignsB
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts

/-! # Data -/

namespace OAI.NumberTheory.ArithmeticGroups.Data.CongruenceLevel

noncomputable section

/-!
CongruenceLevel definitions, copied from the committed specification with declaration-equivalent
repairs: `Σ` is renamed `Place`; imported definitions are rehosted/reused from
proved modules instead of importing statement stubs. No target result is assumed.
The analytical torus model and diagonal Hermitian form are unchanged.
-/
open scoped Classical
open OAI.Geometry.ComplexBall.PrescribedSignsB
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

abbrev VE (E : Type*) := Fin 3 → E

variable {E Place : Type*}
  [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Fintype Place]

def hermitian (b : E) (x y : VE E) : E :=
  ∑ i, (if i = 2 then b else 1) * x i *
    NumberField.IsCMField.complexConj E (y i)

def IsProjectiveComplexTorus (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] (Λ : AddSubgroup V) : Prop :=
  ∃ (n : ℕ) (f : V ⧸ Λ → Projectivization ℂ (Fin (n + 1) → ℂ)),
    Topology.IsClosedEmbedding f ∧
    ∀ z : V, ∃ i : Fin (n + 1),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) ∧
      DifferentiableAt ℂ
        (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ
        (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z)

/-- A full integral lattice in V, stable under O_E. -/
def FullStableLattice (Λ : Submodule ℤ (VE E)) : Prop :=
  Λ.FG ∧
  Submodule.span ℚ (Λ : Set (VE E)) = ⊤ ∧
  ∀ (a : NumberField.RingOfIntegers E) (x : VE E),
    x ∈ Λ → (a : E) • x ∈ Λ

/-- Principal congruence level in the unitary isometry group. -/
def PrincipalLevel
    (b : E) (Λ : Submodule ℤ (VE E)) (N : ℕ)
    (g : VE E ≃ₗ[E] VE E) : Prop :=
  (∀ x y,
    hermitian b (g x) (g y) = hermitian b x y) ∧
  (∀ x, x ∈ Λ ↔ g x ∈ Λ) ∧
  ∀ x ∈ Λ, ∃ y ∈ Λ, g x - x = (N : ℤ) • y

/--
Analytic model of a polarized abelian fiber:
the tangent space is the quotient by P; its period lattice comes
from Λ; the integral action descends; and the polarization is ψ.
-/
def AnalyticPolarizedFiber
    (σ : Place → E →ₐ[ℚ] ℂ)
    (Λ : Submodule ℤ (VE E))
    (ψ : VE E → VE E → ℚ)
    (P : Submodule ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place)) : Prop :=
  let T := Fin (3 * Fintype.card Place) → ℂ
  ∃ (π : Geometry.ComplexBall.PrescribedSignsB.Ambient Place →ₗ[ℂ] T)
    (Γ : AddSubgroup T)
    (H : T →ₗ⋆[ℂ] T →ₗ[ℂ] ℂ)
    (ρ : NumberField.RingOfIntegers E →+* Module.End ℂ T),
    π.ker = P ∧
    Function.Surjective π ∧
    Function.Injective (fun x : VE E =>
      π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x)) ∧
    (∀ t : T, t ∈ Γ ↔
      ∃ x : VE E, x ∈ Λ ∧
        t = π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x)) ∧
    DiscreteTopology Γ ∧
    CompactSpace (T ⧸ Γ) ∧
    IsProjectiveComplexTorus T Γ ∧
    (∀ u v : T, H v u = star (H u v)) ∧
    (∀ u : T, u ≠ 0 → 0 < (H u u).re) ∧
    (∀ x y : VE E,
      (H (π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x))
         (π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ y))).im =
        (ψ x y : ℝ)) ∧
    (∀ (a : NumberField.RingOfIntegers E) (x : VE E),
      ρ a (π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x)) =
        π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ ((a : E) • x)))

end

end OAI.NumberTheory.ArithmeticGroups.Data.CongruenceLevel
