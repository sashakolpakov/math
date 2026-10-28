import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.PivotCokernel
import Mathlib.RingTheory.Grassmannian

/-! # Rank -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Rank.Grassmannian

noncomputable section

/-! The cokernel rank on a full matrix-pivot chart is the number of complementary rows. -/

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {μ : Type w} {ν : Type z}
variable [Fintype ι] [Fintype μ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

theorem fullMatrixPivotCokernel_rankAtStalk
    (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν) (hb : Function.Injective b)
    (h : IsUnit (A.submatrix b a).det) (hres : PivotCokernel.Grassmannian.fullPivotResidual A a b = 0) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) ((ν → R) ⧸ (Matrix.toLin' A).range) p =
      Fintype.card ν - Fintype.card ι := by
  classical
  have : Nontrivial R := Function.Surjective.nontrivial
    (f := Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
  rw [congrFun (Module.rankAtStalk_eq_of_equiv (PivotCokernel.Grassmannian.fullMatrixPivotCokernelEquiv A a b h hres)) p,
    Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype_compl]
  have hc : Fintype.card {j : ν // j ∈ Set.range b} = Fintype.card ι :=
    (Fintype.card_congr (Equiv.ofInjective b hb)).symm
  rw [hc]
  rfl

def fullMatrixPivotGrassmannian
    (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν) (hb : Function.Injective b)
    (h : IsUnit (A.submatrix b a).det) (hres : PivotCokernel.Grassmannian.fullPivotResidual A a b = 0) :
    Module.Grassmannian R (ν → R) (Fintype.card ν - Fintype.card ι) := by
  classical
  exact {
    toSubmodule := (Matrix.toLin' A).range
    finite_quotient := inferInstance
    projective_quotient := Module.Projective.of_equiv (PivotCokernel.Grassmannian.fullMatrixPivotCokernelEquiv A a b h hres).symm
    rankAtStalk_eq := fullMatrixPivotCokernel_rankAtStalk A a b hb h hres }

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Rank.Grassmannian
