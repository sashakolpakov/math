import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Cube Line Bundle -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeLineBundle.Construction.CubeCech

noncomputable section

/-! Line bundles as actual locally trivial sheaves of modules on schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits

universe u

def structureSheafModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- A line bundle is a sheaf locally isomorphic to the structure sheaf. -/
def IsLineBundle {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ structureSheafModule U.toScheme)

theorem opensMap_final {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final := by
  let F := TopologicalSpace.Opens.map f.base
  let eY : ⊤_ Y.Opens ≅ (⊤ : Y.Opens) := terminalIsoIsTerminal isTerminalTop
  let eX : ⊤_ X.Opens ≅ (⊤ : X.Opens) := terminalIsoIsTerminal isTerminalTop
  have he : F.obj (⊤ : Y.Opens) = (⊤ : X.Opens) := rfl
  have : PreservesLimit (Functor.empty.{0} Y.Opens) F :=
    preservesTerminal_of_iso F (F.mapIso eY ≪≫ eqToIso he ≪≫ eX.symm)
  infer_instance

/-- Pulling back the structure sheaf as a module gives the structure sheaf. -/
def pullbackStructureSheafIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (structureSheafModule Y) ≅ structureSheafModule X := by
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have : (TopologicalSpace.Opens.map f.base).Final := opensMap_final f
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit
    (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom)
  exact e

theorem isLineBundle_structureSheaf (X : Scheme.{u}) : IsLineBundle (structureSheafModule X) := by
  intro x
  exact ⟨⊤, trivial, ⟨pullbackStructureSheafIso (⊤ : X.Opens).ι⟩⟩

theorem isLineBundle_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (hM : IsLineBundle M) : IsLineBundle N := by
  intro x
  obtain ⟨U, hx, ⟨hU⟩⟩ := hM x
  exact ⟨U, hx, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ hU⟩⟩

/-- Pullback along any scheme morphism preserves line bundles. -/
theorem isLineBundle_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (hM : IsLineBundle M) :
    IsLineBundle ((Scheme.Modules.pullback f).obj M) := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hM (f x)
  let V := f ⁻¹ᵁ U
  refine ⟨V, hx, ⟨?_⟩⟩
  exact ((Scheme.Modules.pullbackComp V.ι f).app M) ≪≫
    ((Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M) ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫
    pullbackStructureSheafIso (f ∣_ U)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeLineBundle.Construction.CubeCech
