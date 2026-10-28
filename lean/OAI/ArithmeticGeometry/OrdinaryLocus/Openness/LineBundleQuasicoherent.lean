import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.CategoryTheory.Sites.Spaces

/-! # Line Bundle Quasicoherent -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent.Construction

noncomputable section

/-! Openness line bundles are locally free and quasicoherent in the native sheaf API. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w

def freeSingletonSheafIso
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    SheafOfModules.free (R := R) PUnit.{u+1} ≅ SheafOfModules.unit R :=
  coproductUniqueIso (fun _ : PUnit.{u+1} ↦ SheafOfModules.unit R)

def unitGeneratingSections
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (SheafOfModules.unit R).GeneratingSections :=
  (SheafOfModules.free.generatingSections PUnit.{u+1}).ofEpi (freeSingletonSheafIso R).hom

theorem unitGeneratingSections_isIso
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsIso (unitGeneratingSections R).π := by
  dsimp [unitGeneratingSections]
  rw [SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  exact IsIso.comp_isIso' (IsIso.id _) (freeSingletonSheafIso R).isIso_hom

/-- A line-bundle chart also trivializes the restriction to the corresponding slice site. -/
def lineBundleOverTrivialization {X : Scheme.{u}} {M : X.Modules}
    (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ LineBundle.Construction.structureSheafModule U.toScheme) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e ≪≫
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm)

theorem exists_finite_local_free_data_of_isLineBundle {X : Scheme.{u}} (M : X.Modules)
    (hM : LineBundle.Construction.IsLineBundle M) :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} M, q.IsLocallyFreeData ∧ q.IsFiniteType := by
  choose U hx e using hM
  let t (x : X) := lineBundleOverTrivialization (U x) (e x).some
  let q : M.LocalGeneratorsData :=
    { I := X
      X := U
      coversTop := by
        rw [_root_.Opens.coversTop_iff]
        change iSup U = ⊤
        apply le_antisymm le_top
        intro x _
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
      generators x := (unitGeneratingSections (X.ringCatSheaf.over (U x))).ofEpi (t x).inv }
  have : q.IsLocallyFreeData := by
    constructor
    intro x
    change IsIso ((unitGeneratingSections (X.ringCatSheaf.over (U x))).ofEpi (t x).inv).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    exact IsIso.comp_isIso' (unitGeneratingSections_isIso (X.ringCatSheaf.over (U x)))
      (t x).isIso_inv
  refine ⟨q, inferInstance, ?_⟩
  constructor
  intro x
  constructor
  change Finite PUnit.{u+1}
  infer_instance

theorem isLocallyFree_of_isLineBundle {X : Scheme.{u}} (M : X.Modules)
    (hM : LineBundle.Construction.IsLineBundle M) : M.IsLocallyFree := by
  obtain ⟨q, hq, _⟩ := exists_finite_local_free_data_of_isLineBundle M hM
  let := hq
  exact q.isLocallyFree

theorem isQuasicoherent_of_isLineBundle {X : Scheme.{u}} (M : X.Modules)
    (hM : LineBundle.Construction.IsLineBundle M) : M.IsQuasicoherent := by
  obtain ⟨q, hq⟩ := (isLocallyFree_of_isLineBundle M hM).exists_isLocallyFreeData
  let := hq
  exact q.quasiCoherentData.isQuasicoherent

/-- Line bundles are finitely presented as sheaves of modules. -/
theorem isFinitePresentation_of_isLineBundle {X : Scheme.{u}} (M : X.Modules)
    (hM : LineBundle.Construction.IsLineBundle M) : M.IsFinitePresentation := by
  obtain ⟨q, hq, hfin⟩ := exists_finite_local_free_data_of_isLineBundle M hM
  let := hq
  refine SheafOfModules.IsFinitePresentation.mk (M := M) ⟨q.quasiCoherentData, ?_⟩
  constructor
  intro i
  constructor
  · exact hfin.isFiniteType i
  · constructor
    change Finite (ULift.{u} Empty)
    infer_instance

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent.Construction
