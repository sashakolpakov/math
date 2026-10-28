import OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-! # Cycle Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CycleCoordinates

noncomputable section

/-! Actual element representatives of abelian cohomology in integer-indexed complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CochainComplex _root_.CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
variable (K : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ)

theorem abelianIntegerCycle_closed (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    x ∈ (K.sc n).g.hom.ker := by
  change K.d n ((ComplexShape.up ℤ).next n) x = 0
  rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)]
  exact hx

def abelianIntegerCycles (x : K.X n) (hx : K.d n (n + 1) x = 0) : K.cycles n :=
  (K.sc n).abCyclesIso.inv ⟨x, abelianIntegerCycle_closed K n x hx⟩

theorem abelianIntegerCycles_i (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    K.iCycles n (abelianIntegerCycles K n x hx) = x :=
  (K.sc n).abCyclesIso_inv_apply_iCycles ⟨x, abelianIntegerCycle_closed K n x hx⟩

def abelianIntegerCycleClass (x : K.X n) (hx : K.d n (n + 1) x = 0) : K.homology n :=
  K.homologyπ n (abelianIntegerCycles K n x hx)

variable {K} {L : CochainComplex AddCommGrpCat.{u} ℤ}

theorem abelianIntegerCycles_map (f : K ⟶ L) (x : K.X n) (hx : K.d n (n + 1) x = 0)
    (hy : L.d n (n + 1) (f.f n x) = 0) :
    HomologicalComplex.cyclesMap f n (abelianIntegerCycles K n x hx) =
      abelianIntegerCycles L n (f.f n x) hy := by
  apply (AddCommGrpCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n)
    (abelianIntegerCycles K n x hx)
  simpa only [ConcreteCategory.comp_apply, abelianIntegerCycles_i] using h

theorem abelianIntegerCycleClass_map (f : K ⟶ L) (x : K.X n) (hx : K.d n (n + 1) x = 0)
    (hy : L.d n (n + 1) (f.f n x) = 0) :
    HomologicalComplex.homologyMap f n (abelianIntegerCycleClass K n x hx) =
      abelianIntegerCycleClass L n (f.f n x) hy := by
  have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n)
    (abelianIntegerCycles K n x hx)
  simp only [ConcreteCategory.comp_apply, abelianIntegerCycles_map n f x hx hy] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CycleCoordinates
