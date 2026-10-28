import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleLocalUnitLifts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleLocality
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.CategoryTheory.Sites.Spaces

/-! # Finite Free Local Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiniteFreeLocalFrames

noncomputable section

section

/-! An actual extension by the structure module splits on algebraic
open neighborhoods. No quasicoherence of its middle term is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def moduleOpenFunctor (X : Scheme.{0}) (U : X.Opens) :
    X.Modules ⥤ SheafOfModules.{0} (X.ringCatSheaf.over U) :=
  SheafOfModules.overFunctor X.ringCatSheaf U

instance moduleOver_additive (X : Scheme.{0}) (U : X.Opens) :
    (moduleOpenFunctor X U).Additive where
  map_add := rfl

instance moduleOver_preservesZeroMorphisms (X : Scheme.{0}) (U : X.Opens) :
    (moduleOpenFunctor X U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

theorem moduleOver_preservesFiniteLimits (X : Scheme.{0}) (U : X.Opens) :
    PreservesFiniteLimits (moduleOpenFunctor X U) := by
  let F := moduleOpenFunctor X U
  let G := (Scheme.Modules.overEquiv U).functor
  have hR : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) :=
    Picard.PoincareBundle.ModuleLocality.restrict_preservesFiniteLimits U.ι
  let : PreservesFiniteLimits (F ⋙ G) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _ (Scheme.Modules.overFunctorEquiv U).symm hR
  exact preservesFiniteLimits_of_reflects_of_preserves F G

theorem moduleOver_preservesFiniteColimits (X : Scheme.{0}) (U : X.Opens) :
    PreservesFiniteColimits (moduleOpenFunctor X U) := by
  let F := moduleOpenFunctor X U
  let G := (Scheme.Modules.overEquiv U).functor
  have hP : PreservesFiniteColimits (Scheme.Modules.pullback U.ι) := inferInstance
  have hR : PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι) :=
    @preservesFiniteColimits_of_natIso _ _ _ _ _ _ (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm hP
  let : PreservesFiniteColimits (F ⋙ G) :=
    @preservesFiniteColimits_of_natIso _ _ _ _ _ _ (Scheme.Modules.overFunctorEquiv U).symm hR
  exact preservesFiniteColimits_of_reflects_of_preserves F G

theorem moduleOver_shortExact {X : Scheme.{0}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (U : X.Opens) :
    (S.map (moduleOpenFunctor X U)).ShortExact := by
  let : PreservesFiniteLimits (moduleOpenFunctor X U) :=
    moduleOver_preservesFiniteLimits X U
  let : PreservesFiniteColimits (moduleOpenFunctor X U) :=
    moduleOver_preservesFiniteColimits X U
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  exact hS.map _

theorem unitQuotientExtension_locally_split {X : Scheme.{0}} {L M : X.Modules}
    (i : L ⟶ M) (p : M ⟶ HilbertConstruction.Line.Bundles.structureModule X) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((ShortComplex.mk i p hip).map (moduleOpenFunctor X U)).Splitting := by
  let : Epi p := hS.epi_g
  obtain ⟨U, hx, z, hz⟩ := ModuleLocalUnitLifts.module_epi_unit_local_lift p x
  have hU := moduleOver_shortExact (ShortComplex.mk i p hip) hS U
  exact ⟨U, hx, ⟨ShortComplex.Splitting.ofExactOfSection _ hU.exact
    (SheafCohomology.Projective.OverGenerator.overGeneratorHom M U z) (ModuleLocalUnitLifts.local_lift_splits_over p U z hz) hU.mono_f⟩⟩

end

/-! Actual finite free frames over algebraic opens provide the original
quasicoherence and finite-type data for module sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

def structureBinaryFreeIso {X : Scheme.{0}} (U : X.Opens) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) (PUnit ⊕ PUnit) ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) ⊞ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (SheafOfModules.freeSumIso PUnit PUnit).symm ≪≫
    coprod.mapIso (coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit (X.ringCatSheaf.over U)))
      (coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit (X.ringCatSheaf.over U))) ≪≫
    (biprod.isoCoprod _ _).symm

def finiteFrameGenerators {X : Scheme.{0}} (M : X.Modules) (U : X.Opens) (J : Type)
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ M.over U) :
    (M.over U).GeneratingSections :=
  (SheafOfModules.free.generatingSections J).ofEpi e.hom

theorem finiteFrameGenerators_isIso {X : Scheme.{0}} (M : X.Modules) (U : X.Opens) (J : Type)
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ M.over U) :
    IsIso (finiteFrameGenerators M U J e).π := by
  unfold finiteFrameGenerators
  rw [SheafOfModules.GeneratingSections.ofEpi_π, SheafOfModules.free.generatingSections_π]
  change IsIso ((𝟙 _) ≫ e.hom)
  rw [Category.id_comp]
  infer_instance

def finiteFreeFrameData {X : Scheme.{0}} (M : X.Modules) {I : Type} (U : I → X.Opens)
    (hU : iSup U = ⊤) (J : Type)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) J ≅ M.over (U i)) :
    M.LocalGeneratorsData where
  I := I
  X := U
  coversTop := by
    rw [Opens.coversTop_iff]
    exact IsOpenCover.mk hU
  generators i := finiteFrameGenerators M (U i) J (e i)

theorem finiteFreeFrameData_locallyFree {X : Scheme.{0}} (M : X.Modules) {I : Type} (U : I → X.Opens)
    (hU : iSup U = ⊤) (J : Type)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) J ≅ M.over (U i)) :
    (finiteFreeFrameData M U hU J e).IsLocallyFreeData where
  isIso i := finiteFrameGenerators_isIso M (U i) J (e i)

theorem finiteFreeFrameData_coherent {X : Scheme.{0}} (M : X.Modules) {I : Type} (U : I → X.Opens)
    (hU : iSup U = ⊤) (J : Type) [Finite J]
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) J ≅ M.over (U i)) :
    M.IsQuasicoherent ∧ M.IsFiniteType := by
  let q := finiteFreeFrameData M U hU J e
  let : q.IsLocallyFreeData := finiteFreeFrameData_locallyFree M U hU J e
  refine ⟨q.quasiCoherentData.isQuasicoherent, ⟨q, ?_⟩⟩
  constructor
  intro i
  exact ⟨inferInstanceAs (Finite J)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiniteFreeLocalFrames
