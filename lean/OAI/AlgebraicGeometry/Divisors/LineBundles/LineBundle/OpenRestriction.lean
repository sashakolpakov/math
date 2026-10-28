import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Open Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

section

/-! # LineBundleCycles: actual module-sheaf pullback preserves algebraic line bundles -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

def LineBundle.OpenRestriction.Cycles.modulePullbackUnitIso {X Y : Scheme.{0}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (DivisorClass.Chern.Line.Bundles.Construction.structureModule Y) ≅
      DivisorClass.Chern.Line.Bundles.Construction.structureModule X := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward f).IsRightAdjoint)
  have : PreservesLimit (Functor.empty.{0} Y.Opens) (TopologicalSpace.Opens.map f.base) :=
    preservesLimit_of_preserves_limit_cone (isTerminalTop : IsTerminal (⊤ : Y.Opens))
      ((isLimitMapConeEmptyConeEquiv (TopologicalSpace.Opens.map f.base) (⊤ : Y.Opens)).symm
        (show IsTerminal ((TopologicalSpace.Opens.map f.base).obj ⊤) from isTerminalTop))
  have : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  have hu : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  exact @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) hu

def LineBundle.OpenRestriction.Cycles.lineBundlePullbackTrivialization {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (e : M.restrict U.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme)
    (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U) :
    ((Scheme.Modules.pullback f).obj M).restrict V.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule V.toScheme :=
  (Scheme.Modules.restrictFunctorIsoPullback V.ι).app ((Scheme.Modules.pullback f).obj M) ≪≫
    (Scheme.Modules.pullbackComp V.ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (f.resLE_comp_ι hV).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (f.resLE U V hV) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (f.resLE U V hV)).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ e) ≪≫
    LineBundle.OpenRestriction.Cycles.modulePullbackUnitIso (f.resLE U V hV)

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.pullback {X Y : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y) (f : X ⟶ Y) :
    LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X where
  sheaf := (Scheme.Modules.pullback f).obj L.sheaf
  locallyTrivial x :=
    ⟨f ⁻¹ᵁ L.trivializingOpen (f x), L.mem_trivializingOpen (f x),
      ⟨LineBundle.OpenRestriction.Cycles.lineBundlePullbackTrivialization f L.sheaf (L.trivializingOpen (f x))
        (L.trivialization (f x)) _ le_rfl⟩⟩

end

/-!
# LineBundleCycles: restriction of actual algebraic line bundles to open subschemes

The restricted local trivializations are obtained using the genuine restriction
functors and their composition isomorphisms. This applies to arbitrary open subschemes, including singular integral supports.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace LineBundle.OpenRestriction.Cycles.LineBundleConstruction

/-- Pull a genuine local frame back along an open immersion. -/
def restrictFrameAlongOpen {X Y : Scheme} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (U : X.Opens) (e : M.restrict U.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme) :
    (M.restrict f).restrict (f ⁻¹ᵁ U).ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule (f ⁻¹ᵁ U).toScheme :=
  ((Scheme.Modules.restrictFunctorComp (f ⁻¹ᵁ U).ι f).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι f U).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (f ∣_ U) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (f ∣_ U)).mapIso e ≪≫ Scheme.Modules.restrictUnitIso (f ∣_ U)

end LineBundle.OpenRestriction.Cycles.LineBundleConstruction

variable {X : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

/-- Restriction of the actual module sheaf, with its induced rank-one local frames. -/
def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.restrictToOpen {Y : Scheme.{0}} (f : Y ⟶ X)
    [IsOpenImmersion f] : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y where
  sheaf := L.sheaf.restrict f
  locallyTrivial y := ⟨f ⁻¹ᵁ L.trivializingOpen (f y), L.mem_trivializingOpen (f y),
    ⟨LineBundle.OpenRestriction.Cycles.LineBundleConstruction.restrictFrameAlongOpen f L.sheaf (L.trivializingOpen (f y)) (L.trivialization (f y))⟩⟩

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.restrictToOpenPullbackIso {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] :
    (L.restrictToOpen f).sheaf ≅ (L.pullback f).sheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback f).app L.sheaf

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
