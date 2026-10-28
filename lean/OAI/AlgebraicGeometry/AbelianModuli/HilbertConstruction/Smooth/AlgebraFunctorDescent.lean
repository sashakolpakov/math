import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AlgebraFunctorRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineDiagramDescent
import Mathlib.Basic.Finite.Sigma

/-! # Algebra Functor Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AlgebraFunctorDescent

noncomputable section

/-! A finite thin diagram of smooth algebras with open spectrum maps descends as a functor over finite coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

theorem exists_smoothAlgebraFunctorModel_above
    (R : Type u) [CommRing R] {J : Type v} [Category.{w} J] [Finite J] [Quiver.IsThin J]
    (A : J ⥤ CommAlgCat.{u} R) [∀ i, Algebra.Smooth R (A.obj i)]
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (Spec.map (CommRingCat.ofHom (A.map f).hom.toRingHom))]
    (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ M : AlgebraFunctorModel.SmoothAlgebraFunctorModel R A, C ≤ M.coefficients := by
  have : Finite (Σ i j : J, i ⟶ j) := inferInstance
  exact AffineDiagramDescent.exists_smoothAffineDiagramModel_above R (fun i => ↥(A.obj i))
    (fun k : Σ i j : J, i ⟶ j => k.1) (fun k => k.2.1) (fun k => (A.map k.2.2).hom) C

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AlgebraFunctorDescent
