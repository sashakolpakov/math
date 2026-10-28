import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.ModuleMono
import OAI.AlgebraicGeometry.FormalGeometry.Completion.TensorSectionRestriction
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.CoefficientLinear
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSectionComparison
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalAffineFrame

/-! # Tensor Section Mono -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.TensorSectionMono

noncomputable section

/-! A regular affine frame coefficient makes the actual restricted tensor-section map monic. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory Opposite

namespace Construction

universe u

attribute [local instance] SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

theorem tensorSectionMap_restrict_mono_of_regular_coefficient
    {X : Scheme.{u}} {P : X.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P) (M : X.Modules)
    [M.IsQuasicoherent] [(P ⊗ M).IsQuasicoherent]
    (U : X.affineOpens)
    (e : P.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (hr : Function.Injective (fun x : Γ(M, U.1) =>
      Frame.CoefficientLinear.Construction.frameCoefficientLinear P U.1 e (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P s) • x)) :
    Mono ((Scheme.Modules.restrictFunctor U.1.ι).map (TensorSectionMap.Construction.tensorSectionMap s M)) := by
  have : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.restrictFunctor U.1.ι
  let sU := (Scheme.Modules.restrictUnitIso U.1.ι).inv ≫ F.map s
  let eU := SheafCohomology.Projective.FrameSections.restrictTrivializationOfOverIso P U.1 e
  let r := Frame.CoefficientLinear.Construction.frameCoefficientLinear P U.1 e (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P s)
  have hs : SheafCohomology.Projective.TensorFrameSections.poleTopSectionHom P (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P s) = s := by
    apply SheafCohomology.Projective.TensorFrameSections.poleUnitObj_hom_ext_top
    rw [SheafCohomology.Projective.TensorFrameSections.poleTopSectionHom_app_top_apply_one]
    rfl
  have hsU : sU.app ⊤ (1 : Γ(U.1.toScheme, ⊤)) =
      SheafCohomology.Projective.FrameSections.localTrivializationRestriction P U (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P s) := by
    have hh := SheafCohomology.Projective.TensorFrameSections.poleTopSectionHom_localTrivializationRestriction P U (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P s)
    rw [hs] at hh
    have hh' := congrArg (fun a => a.app ⊤ (1 : Γ(U.1.toScheme, ⊤))) hh
    exact hh'.symm.trans (SheafCohomology.Projective.TensorFrameSections.poleTopSectionHom_app_top_apply_one _ _)
  have hc : (show Γ(U.1.toScheme, ⊤) from (sU ≫ eU.hom).app ⊤ (1 : Γ(U.1.toScheme, ⊤))) =
      SheafCohomology.Projective.FrameSections.affineOpenTopSection U r := by
    change eU.hom.app ⊤ (sU.app ⊤ (1 : Γ(U.1.toScheme, ⊤))) = _
    rw [hsU]
    apply SheafCohomology.Projective.FrameSectionComparison.localTrivializationTopSection_unitHom_apply_one P U s e r
    apply Quotients.FiniteDescent.OverSection.Construction.OverSectionLocus.coordinate_eq
    exact (Frame.CoefficientLinear.Construction.frameCoefficientLinear_section s U.1 e).symm
  have hrU : Function.Injective (fun x : Γ(M.restrict U.1.ι, ⊤) =>
      (show Γ(U.1.toScheme, ⊤) from (sU ≫ eU.hom).app ⊤ (1 : Γ(U.1.toScheme, ⊤))) • x) := by
    intro x y h
    apply (ConcreteCategory.bijective_of_isIso (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U.1).hom).1
    apply hr
    have hh := congrArg (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U.1).hom h
    rw [hc, SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso_smul, SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso_smul] at hh
    have hring : U.1.topIso.hom (SheafCohomology.Projective.FrameSections.affineOpenTopSection U r) = r := by
      have ht : SheafCohomology.Projective.FrameSections.affineOpenTopSection U r = U.1.topIso.inv r := by
        unfold SheafCohomology.Projective.FrameSections.affineOpenTopSection
        rw [Scheme.Opens.ι_appIso]
        rfl
      rw [ht, Iso.inv_hom_id_apply]
    rw [hring] at hh
    exact hh
  have hi := TensorSectionMap.Construction.tensorSectionMap_globalSections_injective_of_frame sU (M.restrict U.1.ι) eU hrU
  have hres := TensorSectionRestriction.Construction.restrict_tensorSectionMap U.1.ι s M
  have : (F.obj M).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor U.1.ι M
  have : (F.obj (P ⊗ M)).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor U.1.ι (P ⊗ M)
  apply ModuleMono.Construction.affineModuleMap_mono_of_globalSections_injective
  intro x y h
  apply hi
  have hh := congrArg (fun a => a.app ⊤) hres
  have hx := ConcreteCategory.congr_hom hh x
  have hy := ConcreteCategory.congr_hom hh y
  exact hx.symm.trans ((congrArg ((SheafCohomology.Projective.TensorSections.restrictMonoidalTensorIso U.1.ι P M).hom.app ⊤) h).trans hy)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.TensorSectionMono
