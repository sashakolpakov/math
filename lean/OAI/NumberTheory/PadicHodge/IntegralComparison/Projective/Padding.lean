import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ClosedImmersion
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projectivity

/-! # Padding -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.Padding

noncomputable section

/-! A genuine coordinate hyperplane embedding pads every projective
presentation by one dimension over its original coefficient ring. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane.GradedHilbert OAI.NumberTheory.PadicHodge.IntegralComparison.Projectivity.Construction
universe u
variable (R : Type u) [CommRing R]

theorem irrelevant (n : ℕ) :
    HomogeneousIdeal.irrelevant (AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) ≤
      (HomogeneousIdeal.irrelevant (AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R (n + 1))).map (AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinateGraded R n) := by
  apply (HomogeneousIdeal.irrelevant_le (AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).mpr
  intro d hd p hp
  obtain ⟨q, hq, he⟩ := AlgebraicGeometry.Divisors.LineBundles.Graded.SurjectiveChart.BundleCycles.gradedSurjective_homogeneousPreimage
    (AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinateGraded R n) (AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinate_surjective R n) d p hp
  exact he ▸ Ideal.mem_map_of_mem (AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinateGraded R n).toRingHom
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hd hq)

def inclusion (n : ℕ) : Projectivity.Construction.projectiveSpace R n ⟶ Projectivity.Construction.projectiveSpace R (n + 1) :=
  Proj.map (AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinateGraded R n) (Padding.irrelevant R n)

instance inclusion_closed (n : ℕ) : IsClosedImmersion (inclusion R n) :=
  AlgebraicGeometry.Divisors.LineBundles.Projective.ClosedImmersion.BundleCycles.projectiveMap_isClosedImmersion (AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinateGraded R n)
    (Padding.irrelevant R n) (AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.Hyperplane.GradedHilbert.forgetZeroCoordinate_surjective R n)

theorem inclusion_base (n : ℕ) :
    inclusion R n ≫ Projectivity.Construction.projectiveSpaceToSpec R (n + 1) = Projectivity.Construction.projectiveSpaceToSpec R n := by
  unfold inclusion Projectivity.Construction.projectiveSpaceToSpec
  rw [← Category.assoc, AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase.BundleCycles.projectiveMap_toSpecZero, Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  apply Subtype.ext
  exact MvPolynomial.killCompl_C (Fin.succ_injective (n := n + 1)) z

theorem exists_positive {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (h : Projectivity.Construction.ProjectiveOver R f) :
    ∃ (n : ℕ) (i : X ⟶ Projectivity.Construction.projectiveSpace R (n + 1)),
      IsClosedImmersion i ∧ i ≫ Projectivity.Construction.projectiveSpaceToSpec R (n + 1) = f := by
  obtain ⟨n, i, hi, hf⟩ := h
  let : IsClosedImmersion i := hi
  refine ⟨n, i ≫ inclusion R n, inferInstance, ?_⟩
  rw [Category.assoc, inclusion_base, hf]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.Padding
