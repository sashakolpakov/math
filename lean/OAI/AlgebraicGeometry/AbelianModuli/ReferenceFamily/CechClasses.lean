import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.AnalytificationComplex

/-! # Cech Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechClasses

noncomputable section

/-! Literal cocycles of the algebraic module resolution represent the
original Cech cohomology, and literal boundaries have zero class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {I : Type} (U : I → V.carrier.Opens)

def algebraicCechComplex : CochainComplex AddCommGrpCat.{0} ℕ :=
  (CategoryTheory.cechComplexFunctor U).obj (Cech.TermModules.structureAbelianSheaf V.carrier).obj

local notation "K" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechClasses.algebraicCechComplex V U

theorem algebraicCechCoordinates_closed (n : ℕ) (z : Γ(Cech.TermModules.cechTermModule V.carrier U n, ⊤))
    (hz : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U n).app ⊤ z = 0) :
    (K).d n (n + 1) (Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U n z) = 0 := by
  erw [← Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates_differential, hz, map_zero]
  rfl

def algebraicCechOneClass (z : Γ(Cech.TermModules.cechTermModule V.carrier U 1, ⊤))
    (hz : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 1).app ⊤ z = 0) : (K).homology 1 :=
  (K).homologyπ 1 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 (K) (Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 1 z)
    (algebraicCechCoordinates_closed V U 1 z hz))

theorem algebraicCechOneClass_eq_zero_of_boundary (z : Γ(Cech.TermModules.cechTermModule V.carrier U 1, ⊤))
    (hz : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 1).app ⊤ z = 0)
    (b : Γ(Cech.TermModules.cechTermModule V.carrier U 0, ⊤)) (hb : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 0).app ⊤ b = z) :
    algebraicCechOneClass V U z hz = 0 := by
  have hc : Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 1 z - 0 =
      (K).d 0 1 (Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 0 b) := by
    erw [sub_zero, ← Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates_differential, hb]
  have hzero : (K).d 1 2 0 = 0 := map_zero _
  have he := SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyπ_cyclesMk_eq_of_sub_eq_boundary 0 (K)
    (Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 1 z) 0 (algebraicCechCoordinates_closed V U 1 z hz)
    hzero (Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 0 b) hc
  have hc0 : SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 (K) 0 hzero = 0 := by
    apply (AddCommGrpCat.mono_iff_injective ((K).iCycles 1)).mp inferInstance
    erw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, map_zero]
  exact he.trans ((congrArg ((K).homologyπ 1) hc0).trans (map_zero _))

theorem algebraicCechOneClass_surjective (a : (K).homology 1) :
    ∃ (z : Γ(Cech.TermModules.cechTermModule V.carrier U 1, ⊤))
      (hz : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 1).app ⊤ z = 0), algebraicCechOneClass V U z hz = a := by
  obtain ⟨q, rfl⟩ := (AddCommGrpCat.epi_iff_surjective ((K).homologyπ 1)).mp inferInstance a
  let z := (Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 1).symm ((K).iCycles 1 q)
  have hz : (Cech.ModuleDifferential.cechModuleDifferential V.carrier U 1).app ⊤ z = 0 := by
    apply (Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 2).injective
    erw [Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates_differential, map_zero]
    change (K).d 1 2 (Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 1
      ((Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 1).symm ((K).iCycles 1 q))) = 0
    erw [AddEquiv.apply_symm_apply]
    exact ConcreteCategory.congr_hom ((K).iCycles_d 1 2) q
  refine ⟨z, hz, congrArg ((K).homologyπ 1) ?_⟩
  apply (AddCommGrpCat.mono_iff_injective ((K).iCycles 1)).mp inferInstance
  erw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
  exact (Cech.GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 1).apply_symm_apply _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechClasses
