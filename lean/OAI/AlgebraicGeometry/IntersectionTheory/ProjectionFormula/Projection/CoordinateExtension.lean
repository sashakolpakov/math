import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PartialPairs
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Coordinate Extension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.CoordinateExtension

noncomputable section

/-! Forgetting a newly prepended coordinate preserves coincidence
on the old domain, and coincident new images have the same old base-locus status. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PartialLinear.Projection

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
  (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)

instance finiteType : LocallyOfFiniteType (PartialLinear.Projection.map X k L) := by
  have hc : LocallyOfFiniteType (PartialLinear.Projection.map X k L ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k) := by
    rw [PartialLinear.Projection.over_base]
    infer_instance
  let := hc
  exact locallyOfFiniteType_of_comp _ (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k)

theorem image_closed (x : PartialLinear.Projection.domain X k L) (hx : IsClosed ({x} : Set ((PartialLinear.Projection.domain X k L) : Scheme))) :
    IsClosed ({PartialLinear.Projection.map X k L x} : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace k)) := by
  let : JacobsonSpace (Foundations.Scheme.ProjectiveSpace.projectiveSpace k) :=
    LocallyOfFiniteType.jacobsonSpace (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k)
  exact (PartialLinear.Projection.map X k L).closePoints_subset_preimage_closedPoints hx

theorem coordinates_rename (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (b : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing k) :
    FiniteProjective.FromForms.coordinates X (k + 1) (Fin.cons a L) (MvPolynomial.rename Fin.succ b) =
      FiniteProjective.FromForms.coordinates X k L b := by
  change MvPolynomial.aeval (fun i => (Fin.cons (α := fun _ => Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) a L i).val)
    (MvPolynomial.rename Fin.succ b) = MvPolynomial.aeval (fun i => (L i).val) b
  rw [MvPolynomial.aeval_rename]
  rfl

def shift (b : Foundations.Scheme.ProjectiveSpace.projectiveGrading k 1) : Foundations.Scheme.ProjectiveSpace.projectiveGrading (k + 1) 1 :=
  ⟨MvPolynomial.rename Fin.succ b.val, MvPolynomial.IsHomogeneous.rename_isHomogeneous b.property⟩

theorem coordinate_zero_iff (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (x y : PartialLinear.Projection.domain X (k + 1) (Fin.cons a L))
    (he : PartialLinear.Projection.map X (k + 1) (Fin.cons a L) x = PartialLinear.Projection.map X (k + 1) (Fin.cons a L) y)
    (i : Fin (k + 1)) :
    (L i).val ∈ (X.embedding x.val).asHomogeneousIdeal ↔
      (L i).val ∈ (X.embedding y.val).asHomogeneousIdeal := by
  let b : Foundations.Scheme.ProjectiveSpace.projectiveGrading (k + 1) 1 :=
    ⟨MvPolynomial.X i.succ, Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous (k + 1) i.succ⟩
  have hx := PartialLinear.Projection.homogeneous_mem X (k + 1) (Fin.cons a L) x b
  have hy := PartialLinear.Projection.homogeneous_mem X (k + 1) (Fin.cons a L) y b
  change _ ↔ FiniteProjective.FromForms.coordinates X (k + 1) (Fin.cons a L)
    (MvPolynomial.X i.succ) ∈ (X.embedding x.val).asHomogeneousIdeal at hx
  change _ ↔ FiniteProjective.FromForms.coordinates X (k + 1) (Fin.cons a L)
    (MvPolynomial.X i.succ) ∈ (X.embedding y.val).asHomogeneousIdeal at hy
  rw [FiniteProjective.FromForms.coordinate] at hx hy
  exact hx.symm.trans ((congrArg (fun z : Foundations.Scheme.ProjectiveSpace.projectiveSpace (k + 1) =>
    b.val ∈ z.asHomogeneousIdeal) he).to_iff.trans hy)

theorem domain_status_iff (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (x y : PartialLinear.Projection.domain X (k + 1) (Fin.cons a L))
    (he : PartialLinear.Projection.map X (k + 1) (Fin.cons a L) x = PartialLinear.Projection.map X (k + 1) (Fin.cons a L) y) :
    x.val ∈ PartialLinear.Projection.domain X k L ↔ y.val ∈ PartialLinear.Projection.domain X k L := by
  rw [PartialLinear.Projection.mem_domain, PartialLinear.Projection.mem_domain]
  apply exists_congr
  intro i
  exact not_congr (coordinate_zero_iff X k L a x y he i)

theorem old_images_eq (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (x y : PartialLinear.Projection.domain X k L)
    (hx : IsClosed ({x} : Set ((PartialLinear.Projection.domain X k L) : Scheme)))
    (hy : IsClosed ({y} : Set ((PartialLinear.Projection.domain X k L) : Scheme)))
    (he : PartialLinear.Projection.map X (k + 1) (Fin.cons a L)
        ⟨x.val, PartialPairs.Projection.domain_cons X k L a x.property⟩ =
      PartialLinear.Projection.map X (k + 1) (Fin.cons a L)
        ⟨y.val, PartialPairs.Projection.domain_cons X k L a y.property⟩) :
    PartialLinear.Projection.map X k L x = PartialLinear.Projection.map X k L y := by
  by_contra hn
  obtain ⟨b, hbx, hby⟩ := Closed.PointLinearSeparation.points k (PartialLinear.Projection.map X k L x) (PartialLinear.Projection.map X k L y)
    (image_closed X k L x hx) (image_closed X k L y hy) hn
  have hb := (PartialLinear.Projection.homogeneous_mem X k L x b).mp hbx
  have hx' := PartialLinear.Projection.homogeneous_mem X (k + 1) (Fin.cons a L)
    ⟨x.val, PartialPairs.Projection.domain_cons X k L a x.property⟩ (shift k b)
  have hy' := PartialLinear.Projection.homogeneous_mem X (k + 1) (Fin.cons a L)
    ⟨y.val, PartialPairs.Projection.domain_cons X k L a y.property⟩ (shift k b)
  change _ ↔ FiniteProjective.FromForms.coordinates X (k + 1) (Fin.cons a L)
    (MvPolynomial.rename Fin.succ b.val) ∈ (X.embedding x.val).asHomogeneousIdeal at hx'
  change _ ↔ FiniteProjective.FromForms.coordinates X (k + 1) (Fin.cons a L)
    (MvPolynomial.rename Fin.succ b.val) ∈ (X.embedding y.val).asHomogeneousIdeal at hy'
  rw [coordinates_rename] at hx' hy'
  have hn' := hx'.mpr hb
  rw [he] at hn'
  exact hby ((PartialLinear.Projection.homogeneous_mem X k L y b).mpr (hy'.mp hn'))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.CoordinateExtension
