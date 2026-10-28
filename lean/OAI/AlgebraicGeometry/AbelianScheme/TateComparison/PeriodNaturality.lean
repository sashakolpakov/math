import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PeriodMap
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Period Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PeriodNaturality

noncomputable section

/-! Integral-period division sequences commute with the actual induced
maps of period quotients. Scalar extension gives the completed period map. -/

open scoped TensorProduct

universe u
variable (q : ℕ) [Fact q.Prime]
  {V W : Type u} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  (L : Submodule ℤ V) (M : Submodule ℤ W)
  (f : V →ₗ[ℚ] W) (hf : ∀ x ∈ L, f x ∈ M)

def periodLatticeMap : L →ₗ[ℤ] M :=
  ((f.restrictScalars ℤ).domRestrict L).codRestrict M (fun x => hf x.val x.property)

def periodQuotientMap : (V ⧸ L.toAddSubgroup) →+ (W ⧸ M.toAddSubgroup) :=
  QuotientAddGroup.map L.toAddSubgroup M.toAddSubgroup f.toAddMonoidHom hf

theorem periodTateMap_natural (x : L) :
    Add.Tate.map q (periodQuotientMap L M f hf) (PeriodMap.periodTateMap q L x) =
      PeriodMap.periodTateMap q M (periodLatticeMap L M f hf x) := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  change (QuotientAddGroup.mk' M.toAddSubgroup) (f (((q : ℚ) ^ n)⁻¹ • x.val)) =
    (QuotientAddGroup.mk' M.toAddSubgroup) (((q : ℚ) ^ n)⁻¹ • f x.val)
  exact congrArg (QuotientAddGroup.mk' M.toAddSubgroup) (f.map_smul _ _)

def completedPeriodTateMap :
    ℤ_[q] ⊗[ℤ] L →ₗ[ℤ_[q]] Add.Tate.Module (H := V ⧸ L.toAddSubgroup) q :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℤ_[q] (L →ₗ[ℤ] Add.Tate.Module (H := V ⧸ L.toAddSubgroup) q)
      (PeriodMap.periodTateMap q L))

@[simp] theorem completedPeriodTateMap_tmul (z : ℤ_[q]) (x : L) :
    completedPeriodTateMap q L (z ⊗ₜ[ℤ] x) = z • PeriodMap.periodTateMap q L x := rfl

theorem completedPeriodTateMap_natural :
    (Add.Tate.map q (periodQuotientMap L M f hf)).comp (completedPeriodTateMap q L) =
      (completedPeriodTateMap q M).comp ((periodLatticeMap L M f hf).baseChange ℤ_[q]) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    simp only [LinearMap.comp_apply, completedPeriodTateMap_tmul, LinearMap.baseChange_tmul,
      map_smul, periodTateMap_natural]
  | add x y hx hy => simp only [map_add, hx, hy]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PeriodNaturality
