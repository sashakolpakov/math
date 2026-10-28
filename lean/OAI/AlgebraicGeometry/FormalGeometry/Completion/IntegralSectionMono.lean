import OAI.AlgebraicGeometry.FormalGeometry.Completion.ModuleMapLocalMono
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OverSection
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Integral Section Mono -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralSectionMono

noncomputable section

/-! A section that is a frame on a nonempty open of an integral scheme
is an actual monomorphism from its structure sheaf. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

theorem integral_section_mono_of_nonempty_nonvanishing
    {X : Scheme.{u}} [IsIntegral X] {M : X.Modules}
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (hs : (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : Set X).Nonempty) : Mono s := by
  apply ModuleMapLocalMono.Construction.moduleMap_mono_of_nonempty_affine_sections_injective
  intro U hU
  let V := U.1 ⊓ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s
  have hv : (V : Set X).Nonempty :=
    nonempty_preirreducible_inter U.1.isOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).isOpen hU hs
  have : Nonempty V := hv.to_subtype
  have hvU : V ≤ U.1 := inf_le_left
  have hvs : V ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := inf_le_right
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.ι s) := by
    apply (AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mpr
    rw [AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback]
    apply top_unique
    intro x _
    exact hvs x.2
  have : IsIso (s.over V) := (Quotients.FiniteDescent.OverSection.Construction.OverSectionLocus.isIso_over_iff s V).mpr inferInstance
  let G := SheafOfModules.evaluation (X.ringCatSheaf.over V) (.op (Over.mk (𝟙 V)))
  have hi : Function.Injective (s.app V) :=
    (ModuleCat.mono_iff_injective (G.map (s.over V))).mp inferInstance
  intro a b hab
  apply map_injective_of_isIntegral X (homOfLE hvU)
  apply hi
  have he := congrArg (fun z => M.presheaf.map (homOfLE hvU).op z) hab
  exact (PresheafOfModules.naturality_apply s.val (homOfLE hvU).op a).trans
    (he.trans (PresheafOfModules.naturality_apply s.val (homOfLE hvU).op b).symm)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralSectionMono
