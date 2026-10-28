import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorPoint
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import OAI.AlgebraicGeometry.Foundations.Scheme.HomogeneousEvalMap
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! # Projective Vector Scale -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorScale

noncomputable section

/-!
# Scale independence of actual projective scheme points

The map from nonzero vectors to `Proj` is invariant under nonzero complex
scalars. It therefore descends to mathlib's ordinary projectivization.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {n : ℕ}

/-- The homogeneous prime ideal of the scheme point contains a homogeneous
polynomial exactly when its ordinary evaluation is zero, including degree zero. -/
theorem projectiveVectorPoint_homogeneous_mem_iff
    (v : Fin (n + 1) → ℂ) (hv : v ≠ 0)
    (f : ProjectiveSpace.homogeneousCoordinateRing n) (d : ℕ) (hf : f ∈ ProjectiveSpace.projectiveGrading n d)
    (x : ProjectiveSpace.complexBase) :
    f ∈ (ProjectiveVectorPoint.projectiveVectorPoint v hv x).asHomogeneousIdeal ↔ MvPolynomial.eval v f = 0 := by
  cases d with
  | zero =>
      obtain ⟨c, rfl⟩ : ∃ c : ℂ, f = MvPolynomial.C c :=
        ⟨_, HomogeneousEvalMap.eq_C_of_isHomogeneous_zero hf⟩
      simp only [MvPolynomial.eval_C]
      constructor
      · intro h
        by_contra hc
        let : (ProjectiveVectorPoint.projectiveVectorPoint v hv x).asHomogeneousIdeal.toIdeal.IsPrime :=
          (ProjectiveVectorPoint.projectiveVectorPoint v hv x).isPrime
        exact Ideal.notMem_of_isUnit
          (ProjectiveVectorPoint.projectiveVectorPoint v hv x).asHomogeneousIdeal.toIdeal
          ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C) h
      · intro hc
        simp [hc]
  | succ d =>
      have h := ProjectiveVectorPoint.projectiveVectorPoint_mem_basicOpen_iff v hv f (Nat.succ_pos d) hf x
      change (¬ f ∈ (ProjectiveVectorPoint.projectiveVectorPoint v hv x).asHomogeneousIdeal ↔
        ¬ MvPolynomial.eval v f = 0) at h
      exact not_iff_not.mp h

/-- Nonzero scalar multiplication does not change the underlying Proj point. -/
theorem projectiveVectorPoint_smul_apply
    (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (c : ℂ) (hc : c ≠ 0)
    (hcv : c • v ≠ 0) (x : ProjectiveSpace.complexBase) :
    ProjectiveVectorPoint.projectiveVectorPoint (c • v) hcv x = ProjectiveVectorPoint.projectiveVectorPoint v hv x := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d f hf
  rw [projectiveVectorPoint_homogeneous_mem_iff (c • v) hcv f d hf x,
    projectiveVectorPoint_homogeneous_mem_iff v hv f d hf x]
  exact HomogeneousEvalMap.eval_smul_eq_zero_iff hf hc v

/-- Nonzero scalar multiplication does not change the actual morphism
`Spec ℂ → Proj ℂ[X₀,...,Xₙ]`, not just its underlying point. -/
theorem projectiveVectorPoint_smul
    (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (c : ℂ) (hc : c ≠ 0)
    (hcv : c • v ≠ 0) :
    ProjectiveVectorPoint.projectiveVectorPoint (c • v) hcv = ProjectiveVectorPoint.projectiveVectorPoint v hv := by
  apply ext_of_apply_closedPoint_eq (ProjectiveSpace.projectiveSpaceToBase n)
    (ProjectiveVectorPoint.projectiveVectorPoint_over_base (c • v) hcv) (ProjectiveVectorPoint.projectiveVectorPoint_over_base v hv)
  exact projectiveVectorPoint_smul_apply v hv c hc hcv _

/-- Ordinary complex projective space maps to the actual complex-valued points
of its projective scheme by quotienting the scale-independent vector map. -/
def projectivizationPoint (n : ℕ) :
    Projectivization ℂ (Fin (n + 1) → ℂ) → (ProjectiveSpace.complexBase ⟶ ProjectiveSpace.projectiveSpace n) :=
  Projectivization.lift
    (fun v : {v : Fin (n + 1) → ℂ // v ≠ 0} => ProjectiveVectorPoint.projectiveVectorPoint v.val v.property)
    (by
      intro a b c h
      have hc : c ≠ 0 := by
        intro hc
        apply a.property
        simpa [hc] using h
      have hcb : c • b.val ≠ 0 := by simpa [← h] using a.property
      simpa [h] using projectiveVectorPoint_smul b.val b.property c hc hcb)

@[simp]
theorem projectivizationPoint_mk (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    projectivizationPoint n (Projectivization.mk ℂ v hv) = ProjectiveVectorPoint.projectiveVectorPoint v hv := rfl

/-- Every point obtained by the quotient construction is over the complex base. -/
@[reassoc (attr := simp)]
theorem projectivizationPoint_over_base (p : Projectivization ℂ (Fin (n + 1) → ℂ)) :
    projectivizationPoint n p ≫ ProjectiveSpace.projectiveSpaceToBase n = 𝟙 ProjectiveSpace.complexBase := by
  induction p using Projectivization.ind with
  | h v hv => exact ProjectiveVectorPoint.projectiveVectorPoint_over_base v hv

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorScale
