import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionHom
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenFrames

/-! # Open Section Frame -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: the actual morphism defined by an open section is invertible in every unit-valued frame -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (U : X.Opens) (s : Γ(L.sheaf, U))

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openSectionHom_frame (x : X) (W : U.toScheme.Opens)
    (hW : U.ι ''ᵁ W ≤ L.trivializingOpen x) (r : Γ(U.toScheme, W)) :
    L.openSectionFrame U.ι x W hW ((Module.SectionHom.BundleCycles.moduleSectionHomOnOpen L.sheaf U s).app W r) =
      r * (U.ι.appIso W).hom (L.sectionFrame x (U.ι ''ᵁ W) hW
        (L.sheaf.presheaf.map (homOfLE (Module.SectionHom.BundleCycles.openInclusionImage_le U W)).op s)) := by
  let e := L.openSectionFrame U.ι x W hW
  let t : Γ(L.sheaf.restrict U.ι, W) := (L.sheaf.restrict U.ι).presheaf.map (homOfLE le_top).op (Module.SectionHom.BundleCycles.moduleSectionAsGlobal L.sheaf U s)
  have ht : e t = (U.ι.appIso W).hom (L.sectionFrame x (U.ι ''ᵁ W) hW
      (L.sheaf.presheaf.map (homOfLE (Module.SectionHom.BundleCycles.openInclusionImage_le U W)).op s)) := by
    change (U.ι.appIso W).hom (L.sectionFrame x (U.ι ''ᵁ W) hW t) = _
    exact congrArg (fun z => (U.ι.appIso W).hom (L.sectionFrame x (U.ι ''ᵁ W) hW z))
      (Module.SectionHom.BundleCycles.moduleSectionAsGlobal_restrict L.sheaf U s W)
  calc
    e ((Module.SectionHom.BundleCycles.moduleSectionHomOnOpen L.sheaf U s).app W r) = e (r • t) :=
      congrArg e (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen_app L.sheaf U s W r)
    _ = r * e t := e.map_smul r t
    _ = _ := congrArg (fun z => r * z) ht

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openSectionHom_bijective_frame (x : X) (W : U.toScheme.Opens)
    (hW : U.ι ''ᵁ W ≤ L.trivializingOpen x)
    (hs : IsUnit (L.sectionFrame x (U.ι ''ᵁ W) hW
      (L.sheaf.presheaf.map (homOfLE (Module.SectionHom.BundleCycles.openInclusionImage_le U W)).op s))) :
    Function.Bijective ((Module.SectionHom.BundleCycles.moduleSectionHomOnOpen L.sheaf U s).app W) := by
  let e := L.openSectionFrame U.ι x W hW
  have heq : (fun r : Γ(U.toScheme, W) => e ((Module.SectionHom.BundleCycles.moduleSectionHomOnOpen L.sheaf U s).app W r)) =
      (fun r => r * (U.ι.appIso W).hom (L.sectionFrame x (U.ι ''ᵁ W) hW
        (L.sheaf.presheaf.map (homOfLE (Module.SectionHom.BundleCycles.openInclusionImage_le U W)).op s))) :=
    funext (L.openSectionHom_frame U s x W hW)
  have hb := IsUnit.isUnit_iff_mulRight_bijective.mp (hs.map (U.ι.appIso W).hom.hom)
  have he : Function.Bijective (fun r : Γ(U.toScheme, W) => e ((Module.SectionHom.BundleCycles.moduleSectionHomOnOpen L.sheaf U s).app W r)) :=
    heq.symm ▸ hb
  exact (e.bijective.of_comp_iff' _).mp he

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.sectionFrame_restrict_from_open (x : X) {V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (hV : V ≤ L.trivializingOpen x) :
    L.sectionFrame x W (hWV.trans hV) (L.sheaf.presheaf.map (homOfLE (hWV.trans hVU)).op s) =
      X.presheaf.map (homOfLE hWV).op
        (L.sectionFrame x V hV (L.sheaf.presheaf.map (homOfLE hVU).op s)) := by
  rw [← L.sectionFrame_naturality x hWV hV,
    ← ConcreteCategory.comp_apply, ← L.sheaf.presheaf.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
