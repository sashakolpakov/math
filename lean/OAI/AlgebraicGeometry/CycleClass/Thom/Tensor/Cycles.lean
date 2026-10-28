import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorArbitraryRepresentatives
import OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross
import OAI.AlgebraicTopology.Kunneth.Add

/-! # Cycles -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.Cycles

noncomputable section

/-! Actual tensor cycles in arbitrary degrees, with the original Künneth
normalization, tensor-map naturality, and the native chain associator. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.Add.Construction
open scoped TensorProduct DirectSum

namespace Constructions

variable {k : Type} [Field k]
variable (C D E : ChainComplex (ModuleCat.{0} k) ℕ)

theorem tensor_cycle_closed_at (p q n : ℕ) (hpq : p + q = n)
    (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) :
    ιTensorObj C D p q n hpq (x.val ⊗ₜ[k] y.val) ∈ AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (C ⊗ D) n := by
  cases p with
  | zero =>
      cases q with
      | zero =>
          have hn : n = 0 := by omega
          subst hn
          exact AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _
      | succ q =>
          have hn : n = q + 1 := by omega
          subst hn
          rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
          have h := DivisorClass.Chern.TensorBoundary.tensorBoundary_point_apply C D q x.val y.val
          rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero D (q + 1) q y, TensorProduct.tmul_zero, map_zero] at h
          exact h
  | succ p =>
      cases q with
      | zero =>
          have hn : n = p + 1 := by omega
          subst hn
          rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
          have h := ConcreteCategory.congr_hom (DivisorClass.Chern.TensorBoundary.tensorBoundary_rightZero C D p) (x.val ⊗ₜ[k] y.val)
          change (C ⊗ D).d (p + 1) p (ιTensorObj C D (p + 1) 0 (p + 1) _ _) =
            ιTensorObj C D p 0 p _ (TensorProduct.map (C.d (p + 1) p).hom LinearMap.id _) at h
          rw [TensorProduct.map_tmul, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero C (p + 1) p x,
            TensorProduct.zero_tmul, map_zero] at h
          exact h
      | succ q =>
          have hn : n = p + 1 + (q + 1) := hpq.symm
          subst hn
          change (C ⊗ D).d (p + 1 + (q + 1)) ((ComplexShape.down ℕ).next (p + 1 + (q + 1)))
            (ιTensorObj C D (p + 1) (q + 1) (p + 1 + (q + 1)) rfl (x.val ⊗ₜ[k] y.val)) = 0
          rw [(ComplexShape.down ℕ).next_eq'
            (show (ComplexShape.down ℕ).Rel (p + 1 + (q + 1)) (p + (q + 1)) from by
              change p + (q + 1) + 1 = p + 1 + (q + 1); omega)]
          have h := ConcreteCategory.congr_hom (DivisorClass.Chern.TensorBoundary.tensorBoundary_positive C D p q) (x.val ⊗ₜ[k] y.val)
          change (C ⊗ D).d (p + 1 + (q + 1)) (p + (q + 1))
              (ιTensorObj C D (p + 1) (q + 1) (p + 1 + (q + 1)) _ _) =
            ιTensorObj C D p (q + 1) (p + (q + 1)) _
                (TensorProduct.map (C.d (p + 1) p).hom LinearMap.id _) +
              (-1 : ℤˣ) ^ (p + 1) •
                (ιTensorObj C D (p + 1) q (p + (q + 1)) _
                  (TensorProduct.map LinearMap.id (D.d (q + 1) q).hom _)) at h
          simpa only [TensorProduct.map_tmul, LinearMap.id_apply,
            AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
            map_zero, smul_zero, add_zero] using h

def tensorCycle (p q : ℕ) (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (C ⊗ D) (p + q) :=
  ⟨ιTensorObj C D p q (p + q) rfl (x.val ⊗ₜ[k] y.val), tensor_cycle_closed_at C D p q (p + q) rfl x y⟩

@[simp]
theorem tensorCycle_val (p q : ℕ) (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) :
    (tensorCycle C D p q x y).val =
      ιTensorObj C D p q (p + q) rfl (x.val ⊗ₜ[k] y.val) := rfl

theorem tensorCycle_natural {C' D' : ChainComplex (ModuleCat.{0} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (p q : ℕ) (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (f ⊗ₘ g) (p + q) (tensorCycle C D p q x y) =
      tensorCycle C' D' p q (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap f p x) (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap g q y) := by
  apply Subtype.ext
  exact TripleCross.Constructions.tensorHom_inclusion_apply k f g p q (p + q) rfl x.val y.val

theorem tensorCycle_kunneth (p q : ℕ) (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) :
    AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth C D (p + q)
      (DirectSum.lof k (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q))
        (fun d => C.homology d.val.1 ⊗[k] D.homology d.val.2) ⟨(p, q), rfl⟩
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C p x ⊗ₜ[k] AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass D q y)) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (C ⊗ D) (p + q) (tensorCycle C D p q x y) :=
  DivisorClass.Chern.TensorArbitraryRepresentatives.algebraicKunneth_of_tensor_cycle C D (p + q) ⟨(p, q), rfl⟩ x y
    (tensorCycle C D p q x y) rfl

def tensorCycleAt (p q n : ℕ) (hpq : p + q = n)
    (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (C ⊗ D) n :=
  ⟨ιTensorObj C D p q n hpq (x.val ⊗ₜ[k] y.val), tensor_cycle_closed_at C D p q n hpq x y⟩

@[simp]
theorem tensorCycleAt_val (p q n : ℕ) (hpq : p + q = n)
    (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) :
    (tensorCycleAt C D p q n hpq x y).val =
      ιTensorObj C D p q n hpq (x.val ⊗ₜ[k] y.val) := rfl

theorem tensorCycleAt_natural {C' D' : ChainComplex (ModuleCat.{0} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (p q n : ℕ) (hpq : p + q = n)
    (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (f ⊗ₘ g) n (tensorCycleAt C D p q n hpq x y) =
      tensorCycleAt C' D' p q n hpq (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap f p x) (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap g q y) := by
  apply Subtype.ext
  exact TripleCross.Constructions.tensorHom_inclusion_apply k f g p q n hpq x.val y.val

theorem tensorCycleAt_associator (p q r n : ℕ) (h : (p + q) + r = n)
    (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles E r) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (α_ C D E).hom n
      (tensorCycleAt (C ⊗ D) E (p + q) r n h (tensorCycleAt C D p q (p + q) rfl x y) z) =
      tensorCycleAt C (D ⊗ E) p (q + r) n ((Nat.add_assoc p q r).symm.trans h) x
        (tensorCycleAt D E q r (q + r) rfl y z) := by
  apply Subtype.ext
  exact Associator.Constructions.associator_hom_tensor C D E p q r n h x.val y.val z.val

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.Cycles
