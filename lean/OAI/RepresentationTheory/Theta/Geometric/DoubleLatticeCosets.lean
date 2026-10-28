import OAI.RepresentationTheory.Theta.Geometric.DoubledPeriodLattice
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-! # Double Lattice Cosets -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The intermediate lattice cover has a finite deck group. -/

variable (Φ : Torus.Data.CM.ProjectivePeriodData)

def Torus.Data.CM.ProjectivePeriodData.doublingEnd : Module.End ℤ Φ.periodIntegerLattice :=
  (2 : ℤ) • LinearMap.id

def Torus.Data.CM.ProjectivePeriodData.doubleSublattice : Submodule ℤ Φ.periodIntegerLattice := LinearMap.range Φ.doublingEnd

abbrev Torus.Data.CM.ProjectivePeriodData.doubleSubgroup : AddSubgroup Φ.periodIntegerLattice := Φ.doubleSublattice.toAddSubgroup

theorem Torus.Data.CM.ProjectivePeriodData.mem_doubleSubgroup (l : Φ.periodIntegerLattice) :
    l ∈ Φ.doubleSubgroup ↔ l.val ∈ Φ.doubledLattice := by
  change (∃ m, Φ.doublingEnd m = l) ↔ _
  rw [Φ.mem_doubledLattice]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, by simp [Torus.Data.CM.ProjectivePeriodData.doublingEnd]⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, Subtype.ext ?_⟩
    change (2 : ℤ) • m.val = l.val
    simpa only [two_smul] using hm

instance Torus.Data.CM.ProjectivePeriodData.doubleCosets_finite : Finite (Φ.periodIntegerLattice ⧸ Φ.doubleSubgroup) := by
  have hinj : Function.Injective Φ.doublingEnd := by
    apply LinearMap.lsmul_injective (R := ℤ)
    norm_num
  exact Submodule.finiteQuotientOfFreeOfRankEq Φ.doubleSublattice
    (LinearEquiv.finrank_eq (LinearEquiv.ofInjective Φ.doublingEnd hinj)).symm

instance Torus.Data.CM.ProjectivePeriodData.doubleCosets_fintype : Fintype (Φ.periodIntegerLattice ⧸ Φ.doubleSubgroup) :=
  Fintype.ofFinite _

theorem Torus.Data.CM.ProjectivePeriodData.doubleCoset_eq_iff (l m : Φ.periodIntegerLattice) :
    (QuotientAddGroup.mk l : Φ.periodIntegerLattice ⧸ Φ.doubleSubgroup) = QuotientAddGroup.mk m ↔
      (QuotientAddGroup.mk l.val : Φ.space ⧸ Φ.doubledLattice.toAddSubgroup) = QuotientAddGroup.mk m.val := by
  rw [QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.eq_iff_sub_mem,
    Φ.mem_doubleSubgroup]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric
