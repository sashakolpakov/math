import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionPullbackComposition
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.OpenPullbackSections
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionHom

/-! # Open Section Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Module.OpenSectionPullback.BundleCycles

noncomputable section

/-! # LineBundleCycles: the canonical restriction/pullback isomorphism preserves actual sections on smaller opens -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (M : Y.Modules)

theorem moduleOpenPullbackIso_toOpen (U : Y.Opens) (V : X.Opens) (hV : V ≤ i ⁻¹ᵁ U)
    (s : Γ(M, U)) :
    ((Scheme.Modules.restrictFunctorIsoPullback i).app M).hom.app V
      ((M.restrictAppIso i V).inv (M.presheaf.map
        (homOfLE ((i.image_mono hV).trans (i.image_preimage_le U))).op s)) =
      SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen i M U V hV s := by
  let e := (Scheme.Modules.restrictFunctorIsoPullback i).app M
  have H := ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality (homOfLE hV).op)
    (M.presheaf.map (homOfLE (i.image_preimage_le U)).op s)
  have H' := H.trans (congrArg (((Scheme.Modules.pullback i).obj M).presheaf.map (homOfLE hV).op)
    (OpenPullbackSections.BundleCycles.moduleOpenPullbackIso_section i M U s))
  change e.hom.app V (M.presheaf.map (homOfLE (i.image_mono hV)).op
    (M.presheaf.map (homOfLE (i.image_preimage_le U)).op s)) = _ at H'
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp] at H'
  exact H'

theorem moduleOpenPullbackIso_openGlobal {Y : Scheme.{0}} (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).hom.app ⊤ (SectionHom.BundleCycles.moduleSectionAsGlobal M U s) =
      SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen U.ι M U ⊤ (fun x _ => x.property) s :=
  moduleOpenPullbackIso_toOpen U.ι M U ⊤ (fun x _ => x.property) s

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Module.OpenSectionPullback.BundleCycles
