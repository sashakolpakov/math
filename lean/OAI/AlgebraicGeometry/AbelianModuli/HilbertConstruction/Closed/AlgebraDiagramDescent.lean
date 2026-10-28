import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AffineDiagramMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraTensorFunctor

/-! # Algebra Diagram Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramDescent

noncomputable section

/-! A surjective map between tensor algebra diagrams descends to compatible closed affine charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u v w

theorem exists_closed_algebra_diagram_descent
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {J : Type v} [Category.{w} J] [Finite J] (A B : J ⥤ CommAlgCat.{u} C)
    [∀ i, Algebra.FiniteType C (A.obj i)] [∀ i, Algebra.FiniteType C (B.obj i)]
    [∀ i, Module.Flat C (B.obj i)]
    (φ : A ⋙ AlgebraTensorFunctor.algebraTensorFunctor C R ⟶ B ⋙ AlgebraTensorFunctor.algebraTensorFunctor C R)
    (hφ : ∀ i, Function.Surjective (φ.app i).hom) (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∃ ψ : A ⋙ AlgebraTensorFunctor.algebraTensorFunctor C D ⟶ B ⋙ AlgebraTensorFunctor.algebraTensorFunctor C D,
        (∀ i x, Coefficient.TensorMaps.coefficientTensorMap D ((ψ.app i).hom x) = (φ.app i).hom (Coefficient.TensorMaps.coefficientTensorMap D x)) ∧
        ∃ F : Subalgebra D R, F.FG ∧
          ∀ i, IsClosedImmersion (Spec.map (CommRingCat.ofHom
            (R := F ⊗[D] (D ⊗[C] A.obj i)) (S := F ⊗[D] (D ⊗[C] B.obj i))
            ((Functor.whiskerRight ψ (AlgebraTensorFunctor.algebraTensorFunctor D F)).app i).hom.toRingHom)) := by
  let K := Σ i j : J, i ⟶ j
  let s (k : K) := k.1
  let t (k : K) := k.2.1
  have hn (k : K) : ((φ.app (t k)).hom).comp
        (Algebra.TensorProduct.map (AlgHom.id R R) (A.map k.2.2).hom) =
      (Algebra.TensorProduct.map (AlgHom.id R R) (B.map k.2.2).hom).comp (φ.app (s k)).hom :=
    congrArg (fun f => f.hom) (φ.naturality k.2.2)
  obtain ⟨D, hED, hD, ψ, hψ, hnat, F, hF, hf⟩ := AffineDiagramMaps.exists_common_closed_affine_diagram_maps
    (fun i => ↥(A.obj i)) (fun i => ↥(B.obj i)) s t
    (fun k => (A.map k.2.2).hom) (fun k => (B.map k.2.2).hom)
    (fun i => (φ.app i).hom) hφ hn E hE
  let η : A ⋙ AlgebraTensorFunctor.algebraTensorFunctor C D ⟶ B ⋙ AlgebraTensorFunctor.algebraTensorFunctor C D := {
    app := fun i => CommAlgCat.ofHom (ψ i)
    naturality := fun i j h => CommAlgCat.hom_ext (hnat ⟨i, j, h⟩) }
  exact ⟨D, hED, hD, η, hψ, F, hF, hf⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AlgebraDiagramDescent
