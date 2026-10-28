import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.QuasiIsoCycleLifts
import Mathlib.Algebra.Homology.QuasiIso

/-! # Cochain Low -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CochainLow.CochainLowDegreeLifts

noncomputable section

/-! Concrete degree-zero and degree-one lifts for a quasi-isomorphism
of the original nonnegative module complexes. -/

open _root_.CategoryTheory

universe u v
variable {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)

def zeroMap : K.sc' 0 0 1 ⟶ L.sc' 0 0 1 :=
  (HomologicalComplex.shortComplexFunctor' _ _ 0 0 1).map f

def oneMap : K.sc' 0 1 2 ⟶ L.sc' 0 1 2 :=
  (HomologicalComplex.shortComplexFunctor' _ _ 0 1 2).map f

theorem zero_bijective (hf : QuasiIsoAt f 0) : Function.Bijective (PeriodInvariants.ModuleHomologyMaps.cycleMap (zeroMap f)) :=
  Module.QuasiIsoCycleLifts.ModuleQuasiIsoCycleLifts.zero_cycle_bijective (zeroMap f)
    ((CochainComplex.quasiIsoAt₀_iff f).mp hf)
    (by change K.d 0 0 = 0; simp) (by change L.d 0 0 = 0; simp)

theorem zero_cycle_lift (hf : QuasiIsoAt f 0) (y : L.X 0) (hy : L.d 0 1 y = 0) :
    ∃ x : K.X 0, K.d 0 1 x = 0 ∧ f.f 0 x = y := by
  obtain ⟨x, hx⟩ := (zero_bijective f hf).2 ⟨y, hy⟩
  exact ⟨x.val, x.property, congrArg Subtype.val hx⟩

theorem zero_cycle_injective (hf : QuasiIsoAt f 0) (x : K.X 0) (hx : K.d 0 1 x = 0)
    (hfx : f.f 0 x = 0) : x = 0 := by
  let xc : LinearMap.ker (K.d 0 1).hom := ⟨x, hx⟩
  have h : PeriodInvariants.ModuleHomologyMaps.cycleMap (zeroMap f) xc =
      PeriodInvariants.ModuleHomologyMaps.cycleMap (zeroMap f) 0 := by
    rw [map_zero]
    exact Subtype.ext hfx
  exact congrArg Subtype.val ((zero_bijective f hf).1 h)

theorem one_cycle_lift (hf : QuasiIsoAt f 1) (y : L.X 1) (hy : L.d 1 2 y = 0) :
    ∃ x : K.X 1, K.d 1 2 x = 0 ∧ ∃ b : L.X 0, f.f 1 x - y = L.d 0 1 b :=
  Module.QuasiIsoCycleLifts.ModuleQuasiIsoCycleLifts.cycle_lift (oneMap f)
    ((quasiIsoAt_iff' f 0 1 2 (by simp) (by simp)).mp hf) y hy

theorem one_boundary_lift (hf : QuasiIsoAt f 1) (x : K.X 1) (hx : K.d 1 2 x = 0)
    (b : L.X 0) (hb : f.f 1 x = L.d 0 1 b) : ∃ a : K.X 0, K.d 0 1 a = x :=
  Module.QuasiIsoCycleLifts.ModuleQuasiIsoCycleLifts.boundary_lift (oneMap f)
    ((quasiIsoAt_iff' f 0 1 2 (by simp) (by simp)).mp hf) x hx b hb

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CochainLow.CochainLowDegreeLifts
