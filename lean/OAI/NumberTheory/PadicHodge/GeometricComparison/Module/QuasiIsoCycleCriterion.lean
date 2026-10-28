import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.QuasiIsoCycleLifts

/-! # Quasi Iso Cycle Criterion -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.QuasiIsoCycleCriterion.ModuleQuasiIsoCycleCriterion

noncomputable section

/-! Cycle lifting and boundary detection characterize the original module homology map. -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleHomologyMaps
universe u v
variable {R : Type u} [CommRing R] {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)

theorem quasiIso
    (hsurj : ∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ b : T.X₁, f.τ₂ x - y = T.f b)
    (hinj : ∀ (x : S.X₂), S.g x = 0 →
      ∀ b : T.X₁, f.τ₂ x = T.f b → ∃ a : S.X₁, S.f a = x) : ShortComplex.QuasiIso f := by
  apply (PeriodInvariants.ModuleHomologyMaps.quasiIso_iff_bijective f).mpr
  have hzero : ∀ q, PeriodInvariants.ModuleHomologyMaps.quotientMap f q = 0 → q = 0 := by
    intro q hq
    obtain ⟨x, rfl⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective q
    change (Submodule.Quotient.mk (PeriodInvariants.ModuleHomologyMaps.cycleMap f x) :
      LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) = 0 at hq
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨a, ha⟩ := hinj x.val x.property b (congrArg Subtype.val hb).symm
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, Subtype.ext ha⟩
  constructor
  · intro q r h
    exact sub_eq_zero.mp (hzero (q - r) (by rw [map_sub, h, sub_self]))
  · intro q
    obtain ⟨y, rfl⟩ := (LinearMap.range T.moduleCatToCycles).mkQ_surjective q
    obtain ⟨x, hx, b, hb⟩ := hsurj y.val y.property
    refine ⟨Submodule.Quotient.mk (⟨x, hx⟩ : LinearMap.ker S.g.hom), ?_⟩
    change (Submodule.Quotient.mk (PeriodInvariants.ModuleHomologyMaps.cycleMap f ⟨x, hx⟩) :
      LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) = Submodule.Quotient.mk y
    exact (Submodule.Quotient.eq _).mpr ⟨b, Subtype.ext hb.symm⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.QuasiIsoCycleCriterion.ModuleQuasiIsoCycleCriterion
