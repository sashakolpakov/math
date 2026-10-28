import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenSectionFrame
import OAI.AlgebraicGeometry.Divisors.LineBundles.SheafLocalBijectivity
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalFrame
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenRestriction

/-! # Local Unit Trivialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

section

/-! # LineBundleCycles: a section with genuine unit coordinates on an open cover trivializes the actual line bundle -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (U : X.Opens) (s : Γ(L.sheaf, U))
    {ι : Type} (x : ι → X) (V : ι → X.Opens) (hVU : ∀ i, V i ≤ U)
    (hV : ∀ i, V i ≤ L.trivializingOpen (x i))
    (hcover : ∀ y ∈ U, ∃ i, y ∈ V i)
    (hs : ∀ i, IsUnit (L.sectionFrame (x i) (V i) (hV i)
      (L.sheaf.presheaf.map (homOfLE (hVU i)).op s)))

include hcover hs in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openSectionHom_isIso_of_unit_cover : IsIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen L.sheaf U s) := by
  let F : TopCat.Sheaf Ab.{0} U.toScheme :=
    ⟨(DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme).presheaf,
      (DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme).isSheaf⟩
  let G : TopCat.Sheaf Ab.{0} U.toScheme := ⟨(L.sheaf.restrict U.ι).presheaf, (L.sheaf.restrict U.ι).isSheaf⟩
  let φ : F ⟶ G := ⟨(Module.SectionHom.BundleCycles.moduleSectionHomOnOpen L.sheaf U s).mapPresheaf⟩
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  apply SheafLocalBijectivity.BundleCycles.sheafMap_bijective_of_local φ W
  intro y hy
  obtain ⟨i, hi⟩ := hcover y.val y.property
  refine ⟨W ⊓ (U.ι ⁻¹ᵁ V i), inf_le_left, ⟨hy, hi⟩, ?_⟩
  intro S hS
  have hSV : U.ι ''ᵁ S ≤ V i :=
    (U.ι.image_mono (hS.trans inf_le_right)).trans (U.ι.image_preimage_le (V i))
  apply L.openSectionHom_bijective_frame U s (x i) S (hSV.trans (hV i))
  rw [L.sectionFrame_restrict_from_open U s (x i) (hVU i) hSV (hV i)]
  exact (hs i).map (X.presheaf.map (homOfLE hSV).op).hom

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.unitSectionTrivializationOnOpen :
    L.sheaf.restrict U.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme := by
  letI := L.openSectionHom_isIso_of_unit_cover U s x V hVU hV hcover hs
  exact (asIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen L.sheaf U s)).symm

end

/-! # LineBundleCycles: the actual local trivialization taking a given generator section to one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem LineBundle.LocalUnitTrivialization.Cycles.moduleSectionHomOnOpen_inv_generator {X : Scheme.{0}} (M : X.Modules)
    (U : X.Opens) (s : Γ(M, U)) [IsIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen M U s)] :
    (asIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen M U s)).inv.app ⊤ (Module.SectionHom.BundleCycles.moduleSectionAsGlobal M U s) = (1 : Γ(U.toScheme, ⊤)) := by
  have h := Module.SectionHom.BundleCycles.moduleSectionHom_app_top_one (M.restrict U.ι) (Module.SectionHom.BundleCycles.moduleSectionAsGlobal M U s)
  have hi := congrArg (fun k : DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme ⟶
      DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme => k.app ⊤ (1 : Γ(U.toScheme, ⊤)))
    (asIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen M U s)).hom_inv_id
  exact (congrArg (fun z => (asIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen M U s)).inv.app ⊤ z) h.symm).trans hi

variable {X : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (x : X) (U : X.Opens)
    (hU : U ≤ L.trivializingOpen x) (s : Γ(L.sheaf, U)) (hs : IsUnit (L.sectionFrame x U hU s))

include hU hs in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localUnitSectionHom_isIso : IsIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen L.sheaf U s) := by
  apply L.openSectionHom_isIso_of_unit_cover U s (fun _ : Unit => x) (fun _ => U)
    (fun _ => le_rfl) (fun _ => hU) (fun _ hy => ⟨(), hy⟩)
  intro _
  change IsUnit (L.sectionFrame x U hU (L.sheaf.presheaf.map (𝟙 _) s))
  rw [L.sheaf.presheaf.map_id]
  exact hs

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localUnitSectionTrivialization : L.sheaf.restrict U.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme := by
  letI := L.localUnitSectionHom_isIso x U hU s hs
  exact (asIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen L.sheaf U s)).symm

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localUnitSectionTrivialization_generator :
    LineBundle.GlobalFrame.Cycles.lineBundleGlobalFrame (L := L.restrictToOpen U.ι) (L.localUnitSectionTrivialization x U hU s hs) ⊤
      (Module.SectionHom.BundleCycles.moduleSectionAsGlobal L.sheaf U s) = 1 := by
  let := L.localUnitSectionHom_isIso x U hU s hs
  exact LineBundle.LocalUnitTrivialization.Cycles.moduleSectionHomOnOpen_inv_generator L.sheaf U s

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
