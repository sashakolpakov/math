import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel

/-! # Pair Labels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.PairLabels.CM

/-! The ordered ordinary-reduction labels determine the native IsogenyQuotient
chosen/opposite labels without changing any place or its conjugate. -/

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction

def pairEquiv (s : ℕ) : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Fin s × Bool where
  toFun := Sum.elim (fun v => (v, false)) (fun v => (v, true))
  invFun p := if p.2 then Sum.inr p.1 else Sum.inl p.1
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨v, b⟩; cases b <;> rfl

def labels {s : ℕ} {G : Type*} (a : Fin s × Bool ≃ G) : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ G :=
  (pairEquiv s).trans a

theorem chosen {s : ℕ} {G : Type*} (a : Fin s × Bool ≃ G) (v : Fin s) :
    labels a (.inl v) = a (v, false) := rfl

theorem opposite {s : ℕ} {G : Type*} (a : Fin s × Bool ≃ G) (v : Fin s) :
    labels a (.inr v) = a (v, true) := rfl

theorem swap {s : ℕ} {G : Type*} (a : Fin s × Bool ≃ G) (c : G → G)
    (ha : ∀ v b, a (v, !b) = c (a (v, b))) (v : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s) :
    labels a (Sum.swap v) = c (labels a v) := by
  cases v with
  | inl v => exact ha v false
  | inr v => exact ha v true

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.PairLabels.CM
