import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSchemeDiagrams
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramRecovery

/-! # Algebra Diagram Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramModel

noncomputable section

/-! A closed affine diagram model includes finite coefficients and actual isomorphisms after recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

structure ClosedAlgebraDiagramModel
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {J : Type v} [Category.{w} J] (A B : Jᵒᵖ ⥤ CommAlgCat.{u} C) where
  coefficients : Subalgebra C R
  finiteType : coefficients.FG
  map : A ⋙ AlgebraTensorFunctor.algebraTensorFunctor C coefficients ⟶ B ⋙ AlgebraTensorFunctor.algebraTensorFunctor C coefficients
  closingCoefficients : Subalgebra coefficients R
  closingFiniteType : closingCoefficients.FG
  closed : ∀ i, IsClosedImmersion ((AlgebraSchemeDiagrams.algebraSchemeDiagramMap closingCoefficients
    (Functor.whiskerRight map (AlgebraTensorFunctor.algebraTensorFunctor coefficients closingCoefficients))).app i).left
  recovered : ∀ i, IsIso ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap closingCoefficients R)))).map
      ((AlgebraSchemeDiagrams.algebraSchemeDiagramMap closingCoefficients
        (Functor.whiskerRight map (AlgebraTensorFunctor.algebraTensorFunctor coefficients closingCoefficients))).app i))

theorem exists_closedAlgebraDiagramModel
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {J : Type v} [Category.{w} J] [Finite J] (A B : Jᵒᵖ ⥤ CommAlgCat.{u} C)
    [∀ i, Algebra.FiniteType C (A.obj i)] [∀ i, Algebra.FiniteType C (B.obj i)]
    [∀ i, Module.Flat C (B.obj i)]
    (φ : A ⋙ AlgebraTensorFunctor.algebraTensorFunctor C R ⟶ B ⋙ AlgebraTensorFunctor.algebraTensorFunctor C R)
    (hφ : ∀ i, Function.Bijective (φ.app i).hom) (E : Subalgebra C R) (hE : E.FG) :
    ∃ M : ClosedAlgebraDiagramModel (R := R) A B, E ≤ M.coefficients := by
  have : Finite Jᵒᵖ := Finite.of_injective Opposite.unop Opposite.unop_injective
  obtain ⟨D, hED, hD, ψ, hψ, F, hF, hf⟩ :=
    AlgebraDiagramDescent.exists_closed_algebra_diagram_descent A B φ (fun i => (hφ i).2) E hE
  have hd := AlgebraDiagramRecovery.descended_algebra_diagram_recovery_bijective A B φ D ψ hψ hφ
  have hr := AlgebraDiagramRecovery.algebra_diagram_iterated_recovery_bijective ψ F hd
  refine ⟨{
    coefficients := D
    finiteType := hD
    map := ψ
    closingCoefficients := F
    closingFiniteType := hF
    closed := fun i => hf (Opposite.op i)
    recovered := ?_ }, hED⟩
  exact AlgebraSchemeDiagrams.algebraSchemeDiagramMap_pullback_isIso F R
    (Functor.whiskerRight ψ (AlgebraTensorFunctor.algebraTensorFunctor D F)) hr

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramModel
