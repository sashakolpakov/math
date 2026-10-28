import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Arrows
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SchemeDiagramDescent

/-! # Intersection Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.IntersectionModel

noncomputable section

/-! A common smooth noetherian model of every nonempty finite affine intersection and inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R)))
variable [CompactSpace X.left] [IsSeparated X.hom]

abbrev FiniteIntersectionModel :=
  HilbertConstruction.Smooth.AffineDiagramModel.SmoothAffineDiagramModel R
    (fun S => ↥(Affine.OverChartPoints.affineOverAlgebra R (Finite.AffineIntersections.finiteIntersectionChart X S)))
    (Arrows.finiteIntersectionSource X) (Arrows.finiteIntersectionTarget X)
    (fun j => Affine.OverMorphisms.affineOverMap R (Arrows.finiteIntersectionDiagramArrow X j))

def finiteIntersectionModelMap (M : FiniteIntersectionModel X) (S : Finite.AffineIntersections.finiteIntersectionIndex X) :
    (Finite.AffineIntersections.finiteIntersectionChart X S).left ⟶ M.chartScheme S :=
  Affine.SchemeDiagramRecovery.affineDiagramModelMap (Finite.AffineIntersections.finiteIntersectionChart X) (Arrows.finiteIntersectionSource X)
    (Arrows.finiteIntersectionTarget X) (Arrows.finiteIntersectionDiagramArrow X) M S

theorem finiteIntersectionModelMap_isPullback (M : FiniteIntersectionModel X)
    (S : Finite.AffineIntersections.finiteIntersectionIndex X) :
    IsPullback (finiteIntersectionModelMap X M S) (Finite.AffineIntersections.finiteIntersectionChart X S).hom
      (M.chartMap S) (Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom)) :=
  Affine.SchemeDiagramRecovery.affineDiagramModel_isPullback (Finite.AffineIntersections.finiteIntersectionChart X) (Arrows.finiteIntersectionSource X)
    (Arrows.finiteIntersectionTarget X) (Arrows.finiteIntersectionDiagramArrow X) M S

theorem finiteIntersectionModelMap_natural (M : FiniteIntersectionModel X)
    (j : Arrows.finiteIntersectionArrowIndex X) :
    finiteIntersectionModelMap X M (Arrows.finiteIntersectionTarget X j) ≫ M.chartArrow j =
      (Arrows.finiteIntersectionDiagramArrow X j).left ≫
        finiteIntersectionModelMap X M (Arrows.finiteIntersectionSource X j) :=
  Affine.SchemeDiagramRecovery.affineDiagramModel_natural (Finite.AffineIntersections.finiteIntersectionChart X) (Arrows.finiteIntersectionSource X)
    (Arrows.finiteIntersectionTarget X) (Arrows.finiteIntersectionDiagramArrow X) M j

theorem exists_finiteIntersectionModel [Smooth X.hom]
    (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ M : FiniteIntersectionModel X, C ≤ M.coefficients := by
  obtain ⟨M, hM, _, _⟩ := Affine.SchemeDiagramDescent.exists_smooth_affine_scheme_diagram_model R
    (Finite.AffineIntersections.finiteIntersectionChart X) (Arrows.finiteIntersectionSource X) (Arrows.finiteIntersectionTarget X)
    (Arrows.finiteIntersectionDiagramArrow X) C
  exact ⟨M, hM⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.IntersectionModel
