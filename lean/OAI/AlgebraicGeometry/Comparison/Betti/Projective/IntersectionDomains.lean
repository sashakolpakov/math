import OAI.AlgebraicGeometry.Comparison.Betti.ProductCoordinateHigherElimination
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme

/-! # Intersection Domains -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionDomains.Dolbeault

noncomputable section

/-! Standard projective intersections are the actual products of ordinary and
punctured coordinate lines, with the usual coordinate-ratio maps. -/

open _root_.TopologicalSpace Set

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def projectivePatchIntersection (s : Finset ι) : Opens (Projectivization ℂ (ι → ℂ)) where
  carrier := {p | ∀ j ∈ s, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j p}
  is_open' := by
    simpa only [Set.iInter_ofPred] using
      (isOpen_biInter_finset fun j (_ : j ∈ s) => ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch j)

def projectiveIntersectionPunctures (s : Finset ι) (i : ι) : {j : ι // j ≠ i} → Bool :=
  fun j => decide (j.val ∈ s)

theorem mem_projectiveIntersectionProduct (s : Finset ι) (i : ι)
    (z : {j : ι // j ≠ i} → ℂ) :
    z ∈ ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct (projectiveIntersectionPunctures s i) ↔
      ∀ j : {j : ι // j ≠ i}, j.val ∈ s → z j ≠ 0 := by
  rw [ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct, DivisorClass.Chern.Complex.CoordinateSplit.mem_coordinatePolydisc]
  apply forall_congr'
  intro j
  by_cases hj : j.val ∈ s <;>
    simp [projectiveIntersectionPunctures, hj, PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen, PuncturedCauchy.Dolbeault.puncturedComplexOpen]

theorem projectiveIntersection_chart_mem_iff (s : Finset ι) (i : ι) (hi : i ∈ s)
    (p : {p : Projectivization ℂ (ι → ℂ) // Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p}) :
    ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i p ∈
        ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct (projectiveIntersectionPunctures s i) ↔
      p.val ∈ projectivePatchIntersection s := by
  rw [mem_projectiveIntersectionProduct]
  constructor
  · intro h j hj
    by_cases hji : j = i
    · subst j
      exact p.property
    · exact (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i j p.val p.property).mpr (h ⟨j, hji⟩ hj)
  · intro h j hj
    exact (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i j.val p.val (h i hi)).mp (h j.val hj)

def projectiveIntersectionChart (s : Finset ι) (i : ι) (hi : i ∈ s) :
    projectivePatchIntersection s ≃ₜ
      ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct (projectiveIntersectionPunctures s i) where
  toFun p := ⟨ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i ⟨p.val, p.property i hi⟩,
    (projectiveIntersection_chart_mem_iff s i hi _).mpr p.property⟩
  invFun z := ⟨((ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).symm z.val).val,
    (projectiveIntersection_chart_mem_iff s i hi _).mp (by
      simpa only [Homeomorph.apply_symm_apply] using z.property)⟩
  left_inv p := by
    have h := congrArg Subtype.val ((ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).symm_apply_apply
      ⟨p.val, p.property i hi⟩)
    exact Subtype.ext h
  right_inv z := by
    apply Subtype.ext
    exact (ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).apply_symm_apply z.val
  continuous_toFun := (((ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _)
  continuous_invFun := ((continuous_subtype_val.comp
    ((ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i).symm.continuous.comp continuous_subtype_val)).subtype_mk _)

theorem projectiveIntersectionChart_apply (s : Finset ι) (i : ι) (hi : i ∈ s)
    (p : projectivePatchIntersection s) (j : {j : ι // j ≠ i}) :
    (projectiveIntersectionChart s i hi p).val j = Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j.val p.val := rfl

def projectiveSchemeIntersection (n : ℕ) (s : Finset (Fin (n + 1))) :
    Opens (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) where
  carrier := (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm ⁻¹' projectivePatchIntersection s
  is_open' := (projectivePatchIntersection s).isOpen.preimage
    (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.continuous

def projectiveSchemeIntersectionChart (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) :
    projectiveSchemeIntersection n s ≃ₜ
      ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct (projectiveIntersectionPunctures s i) :=
  ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.subtype (fun _ => Iff.rfl)).trans
    (projectiveIntersectionChart s i hi)

theorem projectiveSchemeIntersectionChart_apply (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (p : projectiveSchemeIntersection n s)
    (j : {j : Fin (n + 1) // j ≠ i}) :
    (projectiveSchemeIntersectionChart n s i hi p).val j =
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j.val ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) := rfl

theorem projectiveSchemeIntersectionChart_symm_apply (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s)
    (z : ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct (projectiveIntersectionPunctures s i)) :
    ((projectiveSchemeIntersectionChart n s i hi).symm z).val =
      ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint n i z.val :=
  (ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint_eq_projectivization n i z.val).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionDomains.Dolbeault
