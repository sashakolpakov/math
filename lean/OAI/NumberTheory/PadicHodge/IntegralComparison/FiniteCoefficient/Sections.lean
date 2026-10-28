import OAI.NumberTheory.PadicHodge.IntegralComparison.ConnectedComponentSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf

/-! # Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Sections

noncomputable section

/-! Actual finite-coefficient sections on Noetherian pro-étale objects
form a finite set, since a continuous finite-valued function is constant
on every connected component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction

universe u

variable (ℓ n : ℕ) [Fact ℓ.Prime]

theorem continuous_finite (X : Type*) [TopologicalSpace X] [NoetherianSpace X] :
    Finite C(X, ZMod (ℓ ^ n)) := by
  exact Finite.of_injective
    (ConnectedComponentSections.equiv X (ZMod (ℓ ^ n)) (ZMod (ℓ ^ n)))
    (ConnectedComponentSections.equiv X (ZMod (ℓ ^ n)) (ZMod (ℓ ^ n))).injective

theorem sections_finite {X : Scheme.{u}} (U : X.ProEtᵒᵖ)
    [NoetherianSpace U.unop.left] :
    Finite ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.obj U) := by
  let : Finite C(U.unop.left, ZMod (ℓ ^ n)) := continuous_finite ℓ n U.unop.left
  change Finite (ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ n)))
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Sections
