import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorArbitraryRepresentatives
import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorBoundary

/-! # Homology Tensor Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyTensorNaturality

noncomputable section

/-! The degree-(1,1) Kunneth inclusion is natural. The proof uses
arbitrary actual cycles and the signed tensor differential, so the
chosen cycle representatives in the original splitting add no condition. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped TensorProduct DirectSum

variable (C D : ChainComplex (ModuleCat.{0} ℚ) ℕ)

def tensorCycle11 (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C 1) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D 1) : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (C ⊗ D) 2 :=
  ⟨ιTensorObj C D 1 1 2 rfl (x.val ⊗ₜ[ℚ] y.val), by
    apply (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ (C ⊗ D) 1 _).mpr
    have hx : C.d 1 0 x.val = 0 := (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ C 0 x.val).mp x.property
    have hy : D.d 1 0 y.val = 0 := (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ D 0 y.val).mp y.property
    rw [DivisorClass.Chern.TensorBoundary.tensorBoundary_interval_apply, hx, hy, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, map_zero, map_zero, sub_self]⟩

def tensorHomology11 : C.homology 1 ⊗[ℚ] D.homology 1 →ₗ[ℚ] (C ⊗ D).homology 2 :=
  (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth C D 2).toLinearMap.comp
    (DirectSum.lof ℚ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs 2)
      (fun ij => C.homology ij.val.1 ⊗[ℚ] D.homology ij.val.2) ⟨(1, 1), rfl⟩)

theorem tensorHomology11_cycles (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C 1) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D 1) :
    tensorHomology11 C D (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C 1 x ⊗ₜ[ℚ] AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass D 1 y) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (C ⊗ D) 2 (tensorCycle11 C D x y) :=
  DivisorClass.Chern.TensorArbitraryRepresentatives.algebraicKunneth_of_tensor_cycle C D 2 ⟨(1, 1), rfl⟩ x y (tensorCycle11 C D x y) rfl

variable {C D} {C' D' : ChainComplex (ModuleCat.{0} ℚ) ℕ}

theorem tensorCycle11_map (f : C ⟶ C') (g : D ⟶ D') (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C 1) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D 1) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (f ⊗ₘ g) 2 (tensorCycle11 C D x y) =
      tensorCycle11 C' D' (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap f 1 x) (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap g 1 y) := by
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom (AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom C D f g 2 ⟨(1, 1), rfl⟩)
    (x.val ⊗ₜ[ℚ] y.val)
  change (f ⊗ₘ g).f 2 (ιTensorObj C D 1 1 2 rfl (x.val ⊗ₜ[ℚ] y.val)) =
    ιTensorObj C' D' 1 1 2 rfl (TensorProduct.map (f.f 1).hom (g.f 1).hom (x.val ⊗ₜ[ℚ] y.val)) at h
  rw [TensorProduct.map_tmul] at h
  exact h

theorem tensorHomology11_naturality (f : C ⟶ C') (g : D ⟶ D') (x : C.homology 1) (y : D.homology 1) :
    homologyMap (f ⊗ₘ g) 2 (tensorHomology11 C D (x ⊗ₜ[ℚ] y)) =
      tensorHomology11 C' D' (homologyMap f 1 x ⊗ₜ[ℚ] homologyMap g 1 y) := by
  obtain ⟨x, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C 1 x
  obtain ⟨y, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective D 1 y
  rw [tensorHomology11_cycles, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, tensorCycle11_map,
    ← tensorHomology11_cycles, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyTensorNaturality
