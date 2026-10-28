import OAI.AlgebraicTopology.Kunneth.TensorHomologyD

/-! # Associator -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.Associator

noncomputable section

/-! The native tensor associator on actual homogeneous chain tensors. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped TensorProduct

namespace Constructions

variable {k : Type} [Field k]

theorem associator_hom_tensor (A B C : ChainComplex (ModuleCat.{0} k) ℕ)
    (p q r n : ℕ) (h : (p + q) + r = n)
    (a : A.X p) (b : B.X q) (c : C.X r) :
    (α_ A B C).hom.f n
      (ιTensorObj (A ⊗ B) C (p + q) r n h
        (ιTensorObj A B p q (p + q) rfl (a ⊗ₜ[k] b) ⊗ₜ[k] c)) =
      ιTensorObj A (B ⊗ C) p (q + r) n ((Nat.add_assoc p q r).symm.trans h)
        (a ⊗ₜ[k] ιTensorObj B C q r (q + r) rfl (b ⊗ₜ[k] c)) := by
  have hi := ι_mapBifunctorAssociatorX_hom (curriedAssociatorNatIso (ModuleCat.{0} k))
    A B C (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    p q r n h
  rw [mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ p q r (p + q) n rfl h,
    mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ p q r (q + r) n rfl
      ((Nat.add_assoc p q r).symm.trans h)] at hi
  exact ConcreteCategory.congr_hom hi ((a ⊗ₜ[k] b) ⊗ₜ[k] c)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.Associator
