import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AlgebraFunctorDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.SchemeFunctorRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateDiagramIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineSchemeModels

/-! # Affine Functor Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineFunctorDescent

noncomputable section

/-! Finite thin diagrams of smooth affine schemes descend with open arrows and a natural recovery isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

theorem exists_smooth_affine_functor_model
    (R : Type u) [CommRing R] {J : Type v} [Category.{w} J] [Finite J] [Quiver.IsThin J]
    (F : J ⥤ Over (Spec (.of R))) [∀ i, IsAffine (F.obj i).left] [∀ i, Smooth (F.obj i).hom]
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f).left]
    (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ D : Subalgebra ℤ R, C ≤ D ∧ Algebra.FiniteType ℤ D ∧
      ∃ G : J ⥤ Over (Spec (.of D)), (∀ i, IsAffine (G.obj i).left) ∧
        (∀ i, Smooth (G.obj i).hom) ∧ (∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f).left) ∧
        Nonempty (G ⋙ Over.pullback (Spec.map (CommRingCat.ofHom D.val.toRingHom)) ≅ F) := by
  have : Finite Jᵒᵖ := Finite.of_injective Opposite.unop Opposite.unop_injective
  have (i : Jᵒᵖ) : Algebra.Smooth R ((Affine.CoordinateFunctor.affineCoordinateFunctor R F).obj i) :=
    AffineSchemeModels.affineOverAlgebra_smooth R (F.obj i.unop)
  have {i j : Jᵒᵖ} (f : i ⟶ j) : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((Affine.CoordinateFunctor.affineCoordinateFunctor R F).map f).hom.toRingHom)) :=
    Affine.OverMorphisms.affineOverMap_isOpenImmersion R (F.map f.unop)
  obtain ⟨M, hM⟩ := AlgebraFunctorDescent.exists_smoothAlgebraFunctorModel_above R (Affine.CoordinateFunctor.affineCoordinateFunctor R F) C
  refine ⟨M.coefficients, hM, M.finiteType, M.schemeFunctor, fun i => ?_,
    fun i => M.schemeFunctor_smooth i, fun f => M.schemeFunctor_open f, ?_⟩
  · exact AlgebraSchemeDiagrams.algebraSchemeDiagram_affine _ _ i
  · exact ⟨M.schemeRecoveryIso ≪≫ (Affine.CoordinateDiagramIso.affineCoordinateDiagramIso R F).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineFunctorDescent
