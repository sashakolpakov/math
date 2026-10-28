import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedChartPoint
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.ChartCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialIdealRingMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientFreeBaseChange

/-! # Normalized Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedCriterion.GradedHilbert

noncomputable section

/-! Finite free coordinate quotients over an affine test ring imply the
actual stalkwise conditions defining the normalized Hilbert chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedChartPoint.Grassmannian

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {R : Type u} [CommRing R] {S : Scheme.{u}}

theorem affineNormalizedChartPoint_hilbert_mem (f : Spec (.of R) ⟶ S)
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R)
    (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) (q : ℕ → ℕ)
    (hdeg : ∀ d ∈ BoundedHilbert.DegreeLocus.GradedHilbert.hilbertFlatDegreeSet n (Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)) N,
      Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal (d + N)) ∧
      Hilbert.Polynomial.GradedHilbert.hilbertFunction (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal (d + N) + q d =
        Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N))) :
    NormalizedChartPoint.Grassmannian.affineNormalizedChartPoint f a Q hQ ∈
      (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op (Over.mk f)) := by
  rw [NormalizedHilbert.ChartCriterion.GradedHilbert.normalizedHilbertChart_mem_iff]
  intro d hd t
  rw [NormalizedChartPoint.Grassmannian.affineNormalizedChartPoint_matrix]
  let A := (Spec (.of R)).presheaf.stalk t
  let φ : R →+* A := ((Spec (.of R)).presheaf.Γgerm t).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let : Algebra R A := φ.toAlgebra
  let J := Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q
  let : Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient J.toIdeal (d + N)) := (hdeg d hd).1
  have he : Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) J = Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Q.map φ) :=
    Normalized.PolynomialIdealRingMap.GradedHilbert.normalizedPolynomialIdeal_map φ a Q
  change Module.Flat A (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Q.map φ)).toIdeal (d + N)) ∧
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Q.map φ)).toIdeal (d + N) + q d = _
  rw [← he]
  let := QuotientFreeBaseChange.GradedHilbert.degreeQuotient_free_baseChange (A := A) J (d + N)
  refine ⟨inferInstance, ?_⟩
  rw [QuotientFreeBaseChange.GradedHilbert.degreeQuotient_finrank_baseChange_of_free_ring]
  exact (hdeg d hd).2

theorem existsUnique_affineNormalizedHilbertChartPoint (f : Spec (.of R) ⟶ S)
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R)
    (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) (q : ℕ → ℕ)
    (hdeg : ∀ d ∈ BoundedHilbert.DegreeLocus.GradedHilbert.hilbertFlatDegreeSet n (Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)) N,
      Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal (d + N)) ∧
      Hilbert.Polynomial.GradedHilbert.hilbertFunction (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal (d + N) + q d =
        Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N))) :
    ∃! y : Over.mk f ⟶ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q,
      y ≫ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q = NormalizedChartPoint.Grassmannian.affineNormalizedChartPoint f a Q hQ :=
  (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart_factorization_iff a S q _).mp
    (affineNormalizedChartPoint_hilbert_mem f a Q hQ q hdeg)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedCriterion.GradedHilbert
