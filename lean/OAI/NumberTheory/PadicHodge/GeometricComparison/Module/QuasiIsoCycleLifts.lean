import OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleHomologyMaps
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ZeroDifferentialHomologyMaps

/-! # Quasi Iso Cycle Lifts -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.QuasiIsoCycleLifts.ModuleQuasiIsoCycleLifts

noncomputable section

/-! Explicit cycle and boundary lifts supplied by quasi-isomorphisms of
module short complexes. These are the local steps in the total degree-one comparison. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleHomologyMaps
universe u v
variable {R : Type u} [CommRing R] {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)

theorem cycle_lift (hf : ShortComplex.QuasiIso f) (y : T.X₂) (hy : T.g y = 0) :
    ∃ x : S.X₂, S.g x = 0 ∧ ∃ b : T.X₁, f.τ₂ x - y = T.f b := by
  let yc : LinearMap.ker T.g.hom := ⟨y, hy⟩
  obtain ⟨q, hq⟩ := (PeriodInvariants.ModuleHomologyMaps.quasiIso_iff_bijective f).mp hf |>.2 (Submodule.Quotient.mk yc)
  obtain ⟨x, rfl⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective q
  change (Submodule.Quotient.mk (PeriodInvariants.ModuleHomologyMaps.cycleMap f x) :
    LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) = Submodule.Quotient.mk yc at hq
  obtain ⟨b, hb⟩ := (Submodule.Quotient.eq _).mp hq
  refine ⟨x.val, x.property, b, ?_⟩
  exact (congrArg Subtype.val hb).symm

theorem boundary_lift (hf : ShortComplex.QuasiIso f) (x : S.X₂) (hx : S.g x = 0)
    (b : T.X₁) (hb : f.τ₂ x = T.f b) : ∃ a : S.X₁, S.f a = x := by
  let xc : LinearMap.ker S.g.hom := ⟨x, hx⟩
  have hm : PeriodInvariants.ModuleHomologyMaps.cycleMap f xc ∈ LinearMap.range T.moduleCatToCycles := by
    refine ⟨b, ?_⟩
    exact Subtype.ext hb.symm
  have hq : PeriodInvariants.ModuleHomologyMaps.quotientMap f (Submodule.Quotient.mk xc) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  have hz : (Submodule.Quotient.mk xc :
      LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = 0 :=
    ((PeriodInvariants.ModuleHomologyMaps.quasiIso_iff_bijective f).mp hf).1 (hq.trans (map_zero (PeriodInvariants.ModuleHomologyMaps.quotientMap f)).symm)
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  exact ⟨a, congrArg Subtype.val ha⟩

theorem zero_cycle_bijective (hf : ShortComplex.QuasiIso f) (hS : S.f = 0) (hT : T.f = 0) :
    Function.Bijective (PeriodInvariants.ModuleHomologyMaps.cycleMap f) :=
  (PeriodInvariants.ZeroDifferentialHomologyMaps.quasiIso_iff_cycleMap_bijective f hS hT).mp hf

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.QuasiIsoCycleLifts.ModuleQuasiIsoCycleLifts
