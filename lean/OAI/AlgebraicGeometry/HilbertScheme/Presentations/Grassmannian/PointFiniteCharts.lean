import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.PointPrincipalCharts

/-! # Point Finite Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.PointFiniteCharts

noncomputable section

/-! A finite principal matrix presentation of every affine Grassmannian point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable (R : CommRingCat.{u})

structure FiniteGrassmannianMatrixPresentation
    (g : Over.mk (𝟙 (Spec R)) ⟶ Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R)) where
  index : Type u
  finiteIndex : Fintype index
  denominator : index → R
  columns : index → ι → ν
  matrix : ∀ i, Matrix ι ν (Localization.Away (denominator i))
  normalized : ∀ i, Normalized.Matrices.Grassmannian.IsNormalized (columns i) (matrix i)
  covers : ∀ p : PrimeSpectrum R, ∃ i, denominator i ∉ p.asIdeal
  classifies : ∀ i, (Relative.AffinePoints.relativeAffineScheme R (Localization.Away (denominator i))).hom ≫ g.left =
    (Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R (Localization.Away (denominator i)) (columns i) (matrix i) (normalized i)).left

attribute [instance] FiniteGrassmannianMatrixPresentation.finiteIndex

def grassmannianPointFinitePresentation
    (g : Over.mk (𝟙 (Spec R)) ⟶ Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R)) :
    FiniteGrassmannianMatrixPresentation R g := by
  classical
  apply Classical.choice
  choose r a Q hQ hr he using PointPrincipalCharts.grassmannian_point_principal_chart R g
  have hc : (Set.univ : Set (PrimeSpectrum R)) ⊆ ⋃ p, (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R)) := by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p, hr p⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R)))
    (fun p => (PrimeSpectrum.basicOpen (r p)).isOpen) hc
  refine ⟨{
    index := t
    finiteIndex := inferInstance
    denominator := fun i => r i.val
    columns := fun i => a i.val
    matrix := fun i => Q i.val
    normalized := fun i => hQ i.val
    covers := ?_
    classifies := fun i => he i.val }⟩
  intro p
  obtain ⟨i, hi, hp⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
  exact ⟨⟨i, hi⟩, hp⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.PointFiniteCharts
