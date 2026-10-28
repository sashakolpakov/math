import OAI.Analysis.PDE.Dirichlet.CoordinateTransport
import OAI.Analysis.PDE.Dirichlet.AffineField

/-! Recovery of the missing pure-normal third derivative from the actual
elliptic equation. Every other third derivative is a derivative of a
tangential first derivative, by the proved Schwarz identities. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet

theorem hessian_directional_cycle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} (hu : ContDiff ℝ 3 u) (v w e x : E) :
    fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e)) x v w =
      fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v)) x w e := by
  have h := OAI.Analysis.PDE.Dirichlet.directionalDerivative_triple_comm hu v w e x
  rw [OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 2) (by norm_num) e),
    OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 2) (by norm_num) v)] at h
  exact h

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The known third derivative indexed by a non-pure-normal pair. -/
def tangentThirdEntry (u : EuclideanSpace ℝ I → ℝ) (k i j : I)
    (x : EuclideanSpace ℝ I) : ℝ :=
  if i = k then
    fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single j 1))) x
      (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)
  else
    fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))) x
      (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)

theorem normal_directional_hessian_entry {u : EuclideanSpace ℝ I → ℝ}
    (hu : ContDiff ℝ 3 u) (k i j : I) (x : EuclideanSpace ℝ I) :
    fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = tangentThirdEntry u k i j x := by
  by_cases hi : i = k
  · subst i
    simp only [tangentThirdEntry]
    exact (hessian_directional_cycle hu (EuclideanSpace.single k 1)
      (EuclideanSpace.single k 1) (EuclideanSpace.single j 1) x).symm
  · simp only [tangentThirdEntry, ite_eq_right hi]
    exact hessian_directional_cycle hu _ _ _ _

omit [Fintype I] in
theorem tangentThirdEntry_uses_tangent (k i j : I) (h : (i, j) ≠ (k, k)) :
    (if i = k then j else i) ≠ k := by
  split_ifs with hi
  · intro hj
    exact h (Prod.ext hi hj)
  · exact hi

/-- Solving the normal differentiated equation uses only a nonzero normal
coefficient. In the elliptic application that coefficient is positive. -/
theorem pure_normal_third_eq {u : EuclideanSpace ℝ I → ℝ}
    (hu : ContDiff ℝ 3 u) (A : EuclideanSpace ℝ I → Matrix I I ℝ)
    (k : I) (x : EuclideanSpace ℝ I) (R : ℝ) (hA : A x k k ≠ 0)
    (heq : OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator A
      (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1)) x = R) :
    fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))) x
      (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) =
      (R - ∑ p ∈ (Finset.univ : Finset (I × I)).erase (k, k),
        A x p.1 p.2 * tangentThirdEntry u k p.1 p.2 x) / A x k k := by
  let H := fun p : I × I => A x p.1 p.2 *
    fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))) x
      (EuclideanSpace.single p.1 1) (EuclideanSpace.single p.2 1)
  have hs : (∑ p : I × I, H p) = R := by
    simpa only [H, Fintype.sum_prod_type, OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator] using heq
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (I × I)) H
    (Finset.mem_univ (k, k))
  have hknown : (∑ p ∈ (Finset.univ : Finset (I × I)).erase (k, k), H p) =
      ∑ p ∈ (Finset.univ : Finset (I × I)).erase (k, k),
        A x p.1 p.2 * tangentThirdEntry u k p.1 p.2 x := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [H, normal_directional_hessian_entry hu]
  rw [hs, hknown] at hsplit
  apply (eq_div_iff hA).mpr
  dsimp only [H] at hsplit
  nlinarith

end OAI.Analysis.PDE.Elliptic
