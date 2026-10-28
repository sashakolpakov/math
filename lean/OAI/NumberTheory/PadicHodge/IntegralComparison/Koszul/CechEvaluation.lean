import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology
import Mathlib.Data.Fin.Tuple.Basic

/-! # Cech Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechEvaluation

noncomputable section

/-! The dual exterior Koszul differential, evaluated on an ordered
coordinate wedge, has the same signed deletion formula as the augmented
Čech differential. This fixes the sign of the fraction comparison. -/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction

universe u
variable (R V : Type u) [CommRing R] [AddCommGroup V] [Module R V]
  (l : Module.Dual R V)

theorem ambient (q : ℕ) (v : Fin (q + 1) → V) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l (ExteriorAlgebra.ιMulti R (q + 1) v) =
      ∑ i : Fin (q + 1), ((-1 : R) ^ i.val * l (v i)) •
        ExteriorAlgebra.ιMulti R q (i.removeNth v) := by
  induction q with
  | zero =>
      conv_rhs => rw [Fin.sum_univ_one]
      simp only [Fin.val_zero, pow_zero, one_mul,
        ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
        mul_one]
      exact (CliffordAlgebra.contractLeft_ι 0 l (v 0)).trans
        (Algebra.algebraMap_eq_smul_one _)
  | succ q ih =>
      conv_rhs => rw [Fin.sum_univ_succ]
      rw [ExteriorAlgebra.ιMulti_succ_apply, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction_ι_mul, ih]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.removeNth_zero]
      rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have hv : i.succ.removeNth v = Fin.cons (v 0) (i.removeNth (Fin.tail v)) := by
        ext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp [Fin.removeNth]
        · simp [Fin.removeNth, Fin.tail]
      rw [hv, ExteriorAlgebra.ιMulti_succ_apply]
      simp only [Fin.cons_zero, Fin.val_succ, pow_succ,
        mul_smul_comm, neg_smul, neg_mul, mul_neg, mul_one]
      rfl

 theorem contraction (q : ℕ) (v : Fin (q + 1) → V) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V l q
      (exteriorPower.ιMulti R (q + 1) v) =
      ∑ i : Fin (q + 1), ((-1 : R) ^ i.val * l (v i)) •
        exteriorPower.ιMulti R q (i.removeNth v) := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  exact ambient R V l q v

variable {m : ℕ} (s : Fin m → R)

theorem differential (q : ℕ) (a : Module.Dual R (⋀[R]^q (Fin m → R)))
    (v : Fin (q + 1) → Fin m) :
    (show Module.Dual R (⋀[R]^(q + 1) (Fin m → R)) from
      (OrientedTopCohomology.dualComplex R s).d q (q + 1) a)
        (exteriorPower.ιMulti R (q + 1) (fun i => (Pi.basisFun R (Fin m)) (v i))) =
      ∑ i : Fin (q + 1), ((-1 : R) ^ i.val * s (v i)) •
        a (exteriorPower.ιMulti R q (fun j => (Pi.basisFun R (Fin m)) (v (i.succAbove j)))) := by
  change (show Module.Dual R (⋀[R]^(q + 1) (Fin m → R)) from
    ((OrientedTopCohomology.dualComplex R s).d q (q + 1)).hom a) _ = _
  rw [OrientedTopCohomology.dual_d]
  change a (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _
    (GeneratorMatrix.equation R s) q _) = _
  rw [contraction, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  congr 1
  simp [GeneratorMatrix.equation_apply, Pi.basisFun_apply, Pi.single_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechEvaluation
