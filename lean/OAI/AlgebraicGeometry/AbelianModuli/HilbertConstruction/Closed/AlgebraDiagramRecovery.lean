import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorIsomorphisms

/-! # Algebra Diagram Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramRecovery

noncomputable section

/-! Coefficient-compatible algebra diagrams recover isomorphisms through both scalar extensions. -/

open _root_.CategoryTheory TensorProduct

universe u v w

theorem descended_algebra_diagram_recovery_bijective
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {J : Type v} [Category.{w} J] (A B : J ⥤ CommAlgCat.{u} C)
    (φ : A ⋙ AlgebraTensorFunctor.algebraTensorFunctor C R ⟶ B ⋙ AlgebraTensorFunctor.algebraTensorFunctor C R)
    (D : Subalgebra C R)
    (ψ : A ⋙ AlgebraTensorFunctor.algebraTensorFunctor C D ⟶ B ⋙ AlgebraTensorFunctor.algebraTensorFunctor C D)
    (hψ : ∀ i x, Coefficient.TensorMaps.coefficientTensorMap D ((ψ.app i).hom x) =
      (φ.app i).hom (Coefficient.TensorMaps.coefficientTensorMap D x))
    (hφ : ∀ i, Function.Bijective (φ.app i).hom) :
    ∀ i, Function.Bijective ((AlgebraTensorFunctor.algebraTensorFunctor D R).map (ψ.app i)).hom := by
  intro i
  exact DescendedTensorIsomorphisms.descended_tensorMap_bijective D (φ.app i).hom (ψ.app i).hom (hψ i) (hφ i)

theorem algebra_diagram_iterated_recovery_bijective
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {J : Type v} [Category.{w} J] {A B : J ⥤ CommAlgCat.{u} C}
    (ψ : A ⟶ B) (D : Subalgebra C R)
    (hψ : ∀ i, Function.Bijective ((AlgebraTensorFunctor.algebraTensorFunctor C R).map (ψ.app i)).hom) :
    ∀ i, Function.Bijective ((AlgebraTensorFunctor.algebraTensorFunctor D R).map
      ((Functor.whiskerRight ψ (AlgebraTensorFunctor.algebraTensorFunctor C D)).app i)).hom := by
  intro i
  exact DescendedTensorIsomorphisms.iterated_tensorMap_bijective D (ψ.app i).hom (hψ i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramRecovery
