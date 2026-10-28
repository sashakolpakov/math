import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Homology Classes -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.HomologyClasses

noncomputable section

/-! Explicit module cocycles and their functorial homology classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe v u

variable {R : Type u} [Ring R]
  (S : ShortComplex (ModuleCat.{v} R))

def cycle (x : S.X₂) (hx : S.g x = 0) : S.cycles :=
  S.moduleCatCyclesIso.inv ⟨x, hx⟩

theorem cycle_i (x : S.X₂) (hx : S.g x = 0) : S.iCycles (cycle S x hx) = x := by
  exact ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles ⟨x, hx⟩

def homologyClass (x : S.X₂) (hx : S.g x = 0) : S.homology :=
  S.homologyπ (cycle S x hx)

theorem homologyClass_quotient (x : S.X₂) (hx : S.g x = 0) :
    homologyClass S x hx = S.moduleCatHomologyIso.inv (Submodule.Quotient.mk ⟨x, hx⟩) := by
  exact ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_π ⟨x, hx⟩

theorem homologyClass_surjective (a : S.homology) :
    ∃ (x : S.X₂) (hx : S.g x = 0), homologyClass S x hx = a := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance a
  refine ⟨S.iCycles z, ?_, ?_⟩
  · exact ConcreteCategory.congr_hom S.iCycles_g z
  · have hc : cycle S (S.iCycles z) (ConcreteCategory.congr_hom S.iCycles_g z) = z := by
      apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
      exact cycle_i S _ _
    exact (congrArg S.homologyπ hc).trans hz

variable {S} {T : ShortComplex (ModuleCat.{v} R)}

theorem homologyClass_naturality (f : S ⟶ T) (x : S.X₂) (hx : S.g x = 0) :
    ShortComplex.homologyMap f (homologyClass S x hx) =
      homologyClass T (f.τ₂ x) (by
        have h := ConcreteCategory.congr_hom f.comm₂₃ x
        simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h) := by
  have hz : ShortComplex.cyclesMap f (cycle S x hx) =
      cycle T (f.τ₂ x) (by
        have h := ConcreteCategory.congr_hom f.comm₂₃ x
        simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h) := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    rw [cycle_i]
    have h := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i f) (cycle S x hx)
    simpa only [ConcreteCategory.comp_apply, cycle_i] using h
  have h := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality f) (cycle S x hx)
  simpa only [ConcreteCategory.comp_apply, homologyClass, hz] using h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.HomologyClasses
