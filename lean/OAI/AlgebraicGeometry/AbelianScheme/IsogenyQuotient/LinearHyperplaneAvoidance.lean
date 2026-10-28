import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardProjectiveCharts
import Mathlib.Algebra.Module.Submodule.Union

/-! # Linear Hyperplane Avoidance -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LinearHyperplaneAvoidance.Construction

noncomputable section

/-! Actual linear polynomials avoiding finite sets in the projective
space used by the section construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardProjectiveCharts

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

def sectionLinearPolynomial (c : Fin (n + 1) → R) : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateRing R n :=
  ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i

theorem sectionLinearPolynomial_homogeneous (c : Fin (n + 1) → R) :
    sectionLinearPolynomial c ∈ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n 1 := by
  exact MvPolynomial.IsHomogeneous.sum _ _ _
    (fun i _ => MvPolynomial.isHomogeneous_C_mul_X (c i) i)

theorem sectionLinearPolynomial_eval {B : Type u} [CommRing B]
    (f : R →+* B) (v : Fin (n + 1) → B) (c : Fin (n + 1) → R) :
    MvPolynomial.eval₂Hom f v (sectionLinearPolynomial c) = ∑ i, f (c i) * v i := by
  simp [sectionLinearPolynomial]

def sectionLinearPolynomialMap : (Fin (n + 1) → R) →ₗ[R] AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateRing R n where
  toFun := sectionLinearPolynomial
  map_add' c d := by
    simp [sectionLinearPolynomial, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp [sectionLinearPolynomial, Pi.smul_apply, MvPolynomial.smul_eq_C_mul,
      Finset.mul_sum, mul_assoc]

theorem sectionLinearPolynomial_single (i : Fin (n + 1)) :
    sectionLinearPolynomial (Pi.single i (1 : R)) = MvPolynomial.X i := by
  classical
  simp [sectionLinearPolynomial, Pi.single_apply]

variable {K : Type u} [Field K] [Infinite K]

theorem exists_linear_hyperplane_avoiding (n : ℕ)
    (F : Set (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n).left) (hF : F.Finite) :
    ∃ c : Fin (n + 1) → K,
      ∀ x ∈ F, x ∈ Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading K n) (sectionLinearPolynomial c) := by
  classical
  let : Finite F := hF.to_subtype
  let p (x : F) : Submodule K (Fin (n + 1) → K) :=
    (x.val.asHomogeneousIdeal.toIdeal.restrictScalars K).comap sectionLinearPolynomialMap
  have hp (x : F) : p x ≠ ⊤ := by
    obtain ⟨i, hi⟩ := AbelianModuli.HilbertConstruction.StandardProjectiveCharts.standardProjectiveCharts_cover K n x.val
    have hn := (Proj.mem_basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading K n) (MvPolynomial.X i) x.val).mp hi
    intro htop
    have hm : Pi.single i (1 : K) ∈ p x := htop ▸ Submodule.mem_top
    change sectionLinearPolynomial (Pi.single i (1 : K)) ∈
      x.val.asHomogeneousIdeal.toIdeal at hm
    rw [sectionLinearPolynomial_single] at hm
    exact hn hm
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨c, fun x hx => ?_⟩
  exact (Proj.mem_basicOpen _ _ x).mpr (hc ⟨x, hx⟩)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LinearHyperplaneAvoidance.Construction
