import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily

/-! # Kernel Labels -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels

noncomputable section

/-! Match IsogenyQuotient's disjoint-sum labels with FrobeniusKernel's chosen/opposite
Boolean labels, preserving the original integral coefficient projectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction

def kernelPairLabels (s : ℕ) : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Fin s × Bool where
  toFun := Sum.elim (fun v => (v, false)) (fun v => (v, true))
  invFun := fun v => if v.2 then Sum.inr v.1 else Sum.inl v.1
  left_inv v := by cases v <;> rfl
  right_inv v := by obtain ⟨v, b⟩ := v; cases b <;> rfl

def nativeKernelLabels {s : ℕ} {I : Type*} (labels : (Fin s × Bool) ≃ I) : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ I :=
  (kernelPairLabels s).trans labels

@[simp] theorem nativeKernelLabels_chosen {s : ℕ} {I : Type*}
    (labels : (Fin s × Bool) ≃ I) (v : Fin s) :
    nativeKernelLabels labels (Sum.inl v) = labels (v, false) := rfl

@[simp] theorem nativeKernelLabels_opposite {s : ℕ} {I : Type*}
    (labels : (Fin s × Bool) ≃ I) (v : Fin s) :
    nativeKernelLabels labels (Sum.inr v) = labels (v, true) := rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
