import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CechClasses
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechBoundaryReflection

/-! # Analytification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Analytification

noncomputable section

/-! The comparison from original algebraic Cech cohomology to actual
native holomorphic sheaf H1 is injective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {I : Type} (U : I → V.carrier.Opens) (hU : iSup U = ⊤)

def cechAnalytificationH1 :
    ((CategoryTheory.cechComplexFunctor U).obj (TermModules.structureAbelianSheaf V.carrier).obj).homology 1 ⟶
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of V.analyticSpace)) 1).obj
        (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace) :=
  HomologicalComplex.homologyMap (AnalytificationComplex.cechAnalytificationComplex V U) 1 ≫
    DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf (X := TopCat.of V.analyticSpace) (Intrinsic.CechDifferential.nativeCechCover V U)
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace) (Intrinsic.CechDifferential.nativeCechCover_covers V U hU) 0

theorem cechAnalytificationH1_class (z : Γ(TermModules.cechTermModule V.carrier U 1, ⊤))
    (hz : (ModuleDifferential.cechModuleDifferential V.carrier U 1).app ⊤ z = 0) :
    cechAnalytificationH1 V U hU (CechClasses.algebraicCechOneClass V U z hz) = Intrinsic.CechBoundaryReflection.nativeCechOneClass V U hU z hz := by
  let f := AnalytificationComplex.cechAnalytificationComplex V U
  let x := GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 1 z
  have hx := CechClasses.algebraicCechCoordinates_closed V U 1 z hz
  have hfx := DivisorClass.Chern.Intrinsic.DescentCohomology.abelianCochainMap_closed f 0 x hx
  have he : f.f 1 x = (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj (Intrinsic.CechDifferential.nativeCechCover V U) 1).symm
        (Intrinsic.CechDifferential.nativeCechCochain V U 1 z) := by
    apply (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj
      (Intrinsic.CechDifferential.nativeCechCover V U) 1).injective
    rw [AddEquiv.apply_symm_apply]
    change DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates _ _ 1 (AnalytificationComplex.cechAnalytificationDegree V U 1
      (GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U 1 z)) = _
    rw [AnalytificationComplex.cechAnalytificationDegree_coordinates, AddEquiv.symm_apply_apply]
  change DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf _ _ _ 0
    (HomologicalComplex.homologyMap f 1
      (((CategoryTheory.cechComplexFunctor U).obj (TermModules.structureAbelianSheaf V.carrier).obj).homologyπ 1
        (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 _ x hx))) = _
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk 0 f x hx hfx]
  unfold Intrinsic.CechBoundaryReflection.nativeCechOneClass DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass
  congr 2
  apply (AddCommGrpCat.mono_iff_injective
    (((CategoryTheory.cechComplexFunctor (Intrinsic.CechDifferential.nativeCechCover V U)).obj
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj).iCycles 1)).mp inferInstance
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
  exact he

theorem cechAnalytificationH1_injective : Function.Injective (cechAnalytificationH1 V U hU) := by
  apply (injective_iff_map_eq_zero (cechAnalytificationH1 V U hU).hom).mpr
  intro a ha
  obtain ⟨z, hz, rfl⟩ := CechClasses.algebraicCechOneClass_surjective V U a
  have hn : Intrinsic.CechBoundaryReflection.nativeCechOneClass V U hU z hz =
      (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of V.analyticSpace)) 1).obj
        (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace)) :=
    (cechAnalytificationH1_class V U hU z hz).symm.trans ha
  obtain ⟨b, hb⟩ := Intrinsic.CechBoundaryReflection.algebraicCech_boundary_of_nativeClass_zero V U hU z hz hn
  exact CechClasses.algebraicCechOneClass_eq_zero_of_boundary V U z hz b hb

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Analytification
