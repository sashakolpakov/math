import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlockForms
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.PointIdeal

/-! # Coordinate Block -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlock

noncomputable section

/-! Projection through a coordinate embedding agrees pointwise with
projection by the restricted linear forms, on exactly the same domain. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection

variable {m n r : ℕ} (j : Fin (m + 1) → Fin (n + 1)) (hj : Function.Injective j)
  (L : Fin (r + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)

theorem mem_domain (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace m) :
    CoordinateBlockMap.map j hj x ∈ Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L) ↔
      x ∈ Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates (fun a => CoordinateBlockForms.restrict j (L a))) := by
  simp only [Projective.BasicOpen.RationalProjection.domain, Opens.mem_iSup, Projective.BasicOpen.RationalProjection.coordinateOpen, Proj.mem_basicOpen]
  change (∃ a, CoordinateBlockMap.graded j (Projective.ConeSupport.coordinates L (MvPolynomial.X a)) ∉ x.asHomogeneousIdeal) ↔
    ∃ a, Projective.ConeSupport.coordinates (fun a => CoordinateBlockForms.restrict j (L a)) (MvPolynomial.X a) ∉ x.asHomogeneousIdeal
  apply exists_congr
  intro a
  exact (congrArg (fun p : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m => p ∉ x.asHomogeneousIdeal)
    (DFunLike.congr_fun (CoordinateBlockForms.compose j L) (MvPolynomial.X a))).to_iff

theorem point {S : Scheme} (i : S ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m)
    (hbig : ∀ x, (i ≫ CoordinateBlockMap.map j hj) x ∈ Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L))
    (hsmall : ∀ x, i x ∈ Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates (fun a => CoordinateBlockForms.restrict j (L a))))
    (x : S) :
    Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) (i ≫ CoordinateBlockMap.map j hj) hbig x =
      Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates (fun a => CoordinateBlockForms.restrict j (L a))) i hsmall x := by
  apply ProjectiveSpectrum.ext
  have hbig' := Projection.PointIdeal.ideal (Projective.ConeSupport.coordinates L) (i ≫ CoordinateBlockMap.map j hj) hbig
    (HomogeneousCoordinateMap.ofForms_C _ _) x
  have hsmall' := Projection.PointIdeal.ideal (Projective.ConeSupport.coordinates (fun a => CoordinateBlockForms.restrict j (L a))) i hsmall
    (HomogeneousCoordinateMap.ofForms_C _ _) x
  refine hbig'.trans (Eq.trans ?_ hsmall'.symm)
  change ((i x).asHomogeneousIdeal.comap (CoordinateBlockMap.graded j)).comap (Projective.ConeSupport.coordinates L) =
    (i x).asHomogeneousIdeal.comap (Projective.ConeSupport.coordinates (fun a => CoordinateBlockForms.restrict j (L a)))
  have he := congrArg (fun f : Foundations.Scheme.ProjectiveSpace.projectiveGrading r →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading m => (i x).asHomogeneousIdeal.comap f)
    (CoordinateBlockForms.compose j L)
  exact he

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlock
