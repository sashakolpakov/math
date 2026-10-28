import OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionDomains
import OAI.AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains

/-! # Intersections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.Intersections.Dolbeault

noncomputable section

section

/-! The standard analytic projective cover is the inverse image of the actual
algebraic coordinate cover; its tuple intersections are the proved chart domains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

def projectiveStandardCover (n : ℕ) (i : Fin (n + 1)) :
    Opens (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) := IntersectionDomains.Dolbeault.projectiveSchemeIntersection n {i}

theorem mem_projectiveStandardCover (n : ℕ) (i : Fin (n + 1))
    (p : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) :
    p ∈ projectiveStandardCover n i ↔ Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p) := by
  change (∀ j ∈ ({i} : Finset (Fin (n + 1))), Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j _) ↔ _
  simp only [Finset.mem_singleton, forall_eq]

theorem projectiveStandardCover_eq_analyticOpen (n : ℕ) (i : Fin (n + 1)) :
    projectiveStandardCover n i = Open.AffineIsoEvaluation.analyticOpen
      (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) := by
  ext p
  change (p ∈ projectiveStandardCover n i) ↔ _
  rw [mem_projectiveStandardCover]
  have h := ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen n i
    ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p)
  have hp : ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p) = p :=
    (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).apply_symm_apply p
  rw [hp] at h
  exact h.symm

theorem projectiveStandardCover_covers (n : ℕ) : iSup (projectiveStandardCover n) = ⊤ := by
  apply top_le_iff.mp
  intro p _
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p)
  exact Opens.mem_iSup.mpr ⟨i, (mem_projectiveStandardCover n i p).mpr hi⟩

theorem projectiveStandardCover_tuple_intersection (n p : ℕ)
    (t : Fin (p + 1) → Fin (n + 1)) :
    (∏ᶜ fun k : Fin (p + 1) => projectiveStandardCover n (t k)) =
      IntersectionDomains.Dolbeault.projectiveSchemeIntersection n (Finset.univ.image t) := by
  rw [SheafCohomology.Cech.Cochains.TopologicalSpace.Opens.piObj_eq_iInf]
  apply SetLike.coe_injective
  rw [Opens.coe_iInf]
  ext x
  simp only [Set.mem_iInter]
  change (∀ k, x ∈ projectiveStandardCover n (t k)) ↔ _
  simp only [mem_projectiveStandardCover]
  change (∀ k, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (t k) ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm x)) ↔
    ∀ j ∈ Finset.univ.image t, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm x)
  simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff]

end

/-! Actual finite intersections of algebraic projective coordinate opens
analytify to the independently defined standard analytic intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates OAI.AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation

def projectiveAlgebraicIntersection (n : ℕ) (s : Finset (Fin (n + 1))) :
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens := ⨅ i : s, Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i.val

theorem projectiveAlgebraicIntersection_le (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) :
    projectiveAlgebraicIntersection n s ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i := by
  change (⨅ j : s, Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j.val) ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i
  exact iInf_le (fun j : s => Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j.val) ⟨i, hi⟩

theorem mem_projectiveAlgebraicIntersection (n : ℕ) (s : Finset (Fin (n + 1)))
    (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    x ∈ projectiveAlgebraicIntersection n s ↔ ∀ i ∈ s, x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i := by
  change x ∈ ((projectiveAlgebraicIntersection n s : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens) : Set _) ↔ _
  rw [projectiveAlgebraicIntersection, Opens.coe_iInf]
  simp only [Set.mem_iInter, Subtype.forall]
  rfl

theorem projectiveSchemeIntersection_eq_analyticOpen (n : ℕ) (s : Finset (Fin (n + 1))) :
    IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s = Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (projectiveAlgebraicIntersection n s) := by
  ext p
  change (∀ i ∈ s, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p)) ↔
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ projectiveAlgebraicIntersection n s
  rw [mem_projectiveAlgebraicIntersection]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  change Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p) ↔
    p ∈ Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
  rw [← projectiveStandardCover_eq_analyticOpen]
  exact (mem_projectiveStandardCover n i p).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.Intersections.Dolbeault
