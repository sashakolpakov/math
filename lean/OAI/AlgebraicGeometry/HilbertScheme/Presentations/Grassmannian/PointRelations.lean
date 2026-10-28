import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.PointFiniteCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.MatrixOverlap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverlapMatrixClearing
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.SubmoduleGluing
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.QuotientCoordinates

/-! # Point Relations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian

noncomputable section

/-!
The local matrix kernels of a Grassmannian point glue to a genuine global
submodule of the finite free module, and localization recovers each kernel.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {R : CommRingCat.{u}}
variable {g : Over.mk (𝟙 (Spec R)) ⟶ Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R)}
variable (D : PointFiniteCharts.FiniteGrassmannianMatrixPresentation R g)

def PointFiniteCharts.FiniteGrassmannianMatrixPresentation.relations : Submodule R (ν → R) :=
  Localized.SubmoduleGluing.localizedSubmoduleIntersection
    (fun i => Localized.QuotientCoordinates.Grassmannian.coordinateLocalization (ν := ν) (Submonoid.powers (D.denominator i)))
    (fun i => (Matrix.toLin' (D.matrix i)).ker)

theorem PointFiniteCharts.FiniteGrassmannianMatrixPresentation.clearing :
    Localized.SubmoduleGluing.LocalizedSubmoduleClearing D.denominator
      (fun i => Localized.QuotientCoordinates.Grassmannian.coordinateLocalization (ν := ν) (Submonoid.powers (D.denominator i)))
      (fun i => (Matrix.toLin' (D.matrix i)).ker) := by
  intro i j x hx
  let A := Localization.Away (D.denominator i)
  let C := Localization.Away (D.denominator j)
  let B := Localization.Away (algebraMap R C (D.denominator i))
  have hu : IsUnit (algebraMap R B (D.denominator i)) := by
    rw [IsScalarTower.algebraMap_apply R C B]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R C (D.denominator i))
  let φ : A →ₐ[R] B := IsLocalization.Away.liftAlgHom (D.denominator i)
    (f := Algebra.ofId R B) hu
  let ψ : C →ₐ[R] B := IsScalarTower.toAlgHom R C B
  have hker : (Matrix.toLin' ((D.matrix i).map φ.toRingHom)).ker =
      (Matrix.toLin' ((D.matrix j).map (algebraMap C B))).ker :=
    MatrixOverlap.affine_classifying_common_kernel R φ ψ g.left (D.columns i) (D.columns j) (D.matrix i) (D.matrix j)
      (D.normalized i) (D.normalized j) (D.classifies i) (D.classifies j)
  exact OverlapMatrixClearing.Grassmannian.overlap_matrix_clear_denominator (B := B) (D.denominator i) φ (D.matrix i) (D.matrix j) hker x hx

theorem PointFiniteCharts.FiniteGrassmannianMatrixPresentation.relations_localized (i : D.index) :
    Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R (Localization.Away (D.denominator i))) D.relations =
      (Matrix.toLin' (D.matrix i)).ker := by
  have h := Localized.SubmoduleGluing.localizedSubmoduleIntersection_localized D.denominator
    (fun j => Localized.QuotientCoordinates.Grassmannian.coordinateLocalization (ν := ν) (Submonoid.powers (D.denominator j)))
    (fun j => (Matrix.toLin' (D.matrix j)).ker) D.clearing i
  rw [Submodule.localized'_eq_span] at h
  exact h

omit [Fintype ν] [DecidableEq ν] in
theorem PointFiniteCharts.FiniteGrassmannianMatrixPresentation.denominators_span :
    Ideal.span (Set.range D.denominator) = ⊤ := by
  by_contra h
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (Ideal.span (Set.range D.denominator)) h
  obtain ⟨i, hi⟩ := D.covers ⟨p, hp.isPrime⟩
  exact hi (hle (Ideal.subset_span ⟨i, rfl⟩))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian
