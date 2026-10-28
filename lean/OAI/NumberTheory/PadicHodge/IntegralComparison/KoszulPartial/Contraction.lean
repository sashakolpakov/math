import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CechEvaluation

/-! # Contraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Contraction

noncomputable section

/-! The graded Leibniz rule for an ordered Koszul word. It is the sign
identity for separating ambient equations from point parameters in the
partial fraction comparison. -/
open OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction
universe u
variable (R V : Type u) [CommRing R] [AddCommGroup V] [Module R V]
  (l : Module.Dual R V)

theorem word_mul (p : ℕ) (v : Fin p → V) (x : ExteriorAlgebra R V) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l (ExteriorAlgebra.ιMulti R p v * x) =
      AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l (ExteriorAlgebra.ιMulti R p v) * x +
        (-1 : R) ^ p • (ExteriorAlgebra.ιMulti R p v * AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l x) := by
  induction p with
  | zero =>
      simp only [ExteriorAlgebra.ιMulti_zero_apply, one_mul, pow_zero, one_smul]
      have h : AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l 1 = 0 :=
        CliffordAlgebra.contractLeft_one 0 l
      rw [h, zero_mul, zero_add]
  | succ p ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction_ι_mul,
        ih, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction_ι_mul]
      simp only [mul_add, add_mul, neg_mul, mul_smul_comm, smul_mul_assoc, mul_assoc,
        pow_succ, mul_neg, mul_one, neg_smul, sub_eq_add_neg, neg_add_rev]
      abel

theorem homogeneous_mul (p : ℕ) (v : ⋀[R]^p V) (x : ExteriorAlgebra R V) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l (v.val * x) =
      AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l v.val * x +
        (-1 : R) ^ p • (v.val * AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l x) := by
  have hv : v ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R p : (Fin p → V) → ⋀[R]^p V)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hv using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact word_mul R V l p w x
  | zero => simp
  | add y z _ _ hy hz =>
      simp only [Submodule.coe_add, add_mul, map_add, hy, hz, smul_add]
      abel
  | smul a y _ hy =>
      simp only [Submodule.coe_smul_of_tower, smul_mul_assoc, map_smul, hy, smul_add,
        smul_comm a ((-1 : R) ^ p)]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Contraction
