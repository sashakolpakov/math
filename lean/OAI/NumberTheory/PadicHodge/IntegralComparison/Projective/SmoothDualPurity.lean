import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedCodimension
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PointedPurity

/-! # Smooth Dual Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SmoothDualPurity

noncomputable section

/-! The actual dual negative-twist resolution of a smooth closed
subscheme of projective space is concentrated in its geometric codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
  (j : σ) (B b : ℕ) (hb : b ≤ B) (g : ℕ)
  [SmoothOfRelativeDimension g (f ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

include hb in
omit [LinearOrder σ] in
theorem exactAt (n : ℕ) (hn : n ≠ Fintype.card σ - 1 - g) :
    (ClosedImmersionPurity.internalComplex f j B b).ExactAt n := by
  apply PointedPurity.exactAt f j B b hb (Fintype.card σ - 1 - g) _ n hn
  intro x
  obtain ⟨i, V, hV, hVi, hxV, rs, hrs, hreg, hlen⟩ :=
    Smooth.ClosedCodimension.projective_neighborhood f g x
  exact ⟨i, V, hV, hVi, hxV, rs, hrs, hreg.toIsWeaklyRegular, hlen⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SmoothDualPurity
