import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SchemeDiagramRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineDiagramDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineSchemeModels

/-! # Scheme Diagram Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SchemeDiagramDescent

noncomputable section

/-! Finite diagrams of actual smooth affine schemes descend with Cartesian recovery and compatible arrows. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

theorem exists_smooth_affine_scheme_diagram_model
    (R : Type u) [CommRing R] {I : Type v} [Finite I] (X : I → Over (Spec (.of R)))
    [∀ i, IsAffine (X i).left] [∀ i, Smooth (X i).hom]
    {J : Type w} [Finite J] (s t : J → I) (f : ∀ j, X (t j) ⟶ X (s j))
    [∀ j, IsOpenImmersion (f j).left]
    (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ M : HilbertConstruction.Smooth.AffineDiagramModel.SmoothAffineDiagramModel R (fun i => ↥(OverChartPoints.affineOverAlgebra R (X i))) s t
        (fun j => OverMorphisms.affineOverMap R (f j)),
      C ≤ M.coefficients ∧
      (∀ i, IsPullback (SchemeDiagramRecovery.affineDiagramModelMap X s t f M i) (X i).hom (M.chartMap i)
        (Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom))) ∧
      ∀ j, SchemeDiagramRecovery.affineDiagramModelMap X s t f M (t j) ≫ M.chartArrow j =
        (f j).left ≫ SchemeDiagramRecovery.affineDiagramModelMap X s t f M (s j) := by
  have (i : I) : Algebra.Smooth R (OverChartPoints.affineOverAlgebra R (X i)) := HilbertConstruction.Smooth.AffineSchemeModels.affineOverAlgebra_smooth R (X i)
  have (j : J) : IsOpenImmersion (Spec.map (CommRingCat.ofHom (OverMorphisms.affineOverMap R (f j)).toRingHom)) :=
    OverMorphisms.affineOverMap_isOpenImmersion R (f j)
  obtain ⟨M, hM⟩ := HilbertConstruction.Smooth.AffineDiagramDescent.exists_smoothAffineDiagramModel_above R
    (fun i => ↥(OverChartPoints.affineOverAlgebra R (X i))) s t (fun j => OverMorphisms.affineOverMap R (f j)) C
  exact ⟨M, hM, SchemeDiagramRecovery.affineDiagramModel_isPullback X s t f M, SchemeDiagramRecovery.affineDiagramModel_natural X s t f M⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SchemeDiagramDescent
