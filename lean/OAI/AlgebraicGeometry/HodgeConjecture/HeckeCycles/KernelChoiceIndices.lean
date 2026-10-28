import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroups

/-! # Kernel Choice Indices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceIndices.CM

noncomputable section

/-! Reindex actual kernel choices along proved equalities of their
characters, level and exponents, preserving the underlying subgroups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroups

universe u
variable {R : Type u} [CommRing R] {S : Scheme.{u}} {g N s q : ℕ} [Fact q.Prime]
  (A : AbelianScheme.TateComparison.PEL.PELFamilyData R g N S)
  {χ χ' : Fin s → R →+* ℤ_[q]} {n n' : ℕ} {a a' : Fin s → Fin 3 → ℕ}

def choiceEquiv (hχ : χ = χ') (hn : n = n') (ha : a = a') :
    AbelianScheme.TateComparison.Subgroups.KernelChoices A χ n a ≃ AbelianScheme.TateComparison.Subgroups.KernelChoices A χ' n' a' := by
  subst χ' n' a'
  exact Equiv.refl _

theorem choiceEquiv_subgroup (hχ : χ = χ') (hn : n = n') (ha : a = a')
    (H : AbelianScheme.TateComparison.Subgroups.KernelChoices A χ n a) (v : Fin s) :
    (choiceEquiv A hχ hn ha H).val v = H.val v := by
  subst χ' n' a'
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceIndices.CM
