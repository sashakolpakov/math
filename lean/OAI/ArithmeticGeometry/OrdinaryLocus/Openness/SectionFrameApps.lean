import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OverSection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus

/-! # Section Frame Apps -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionFrameApps.Construction

noncomputable section

/-! A nonvanishing section gives invertible maps on all subordinate opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem section_app_isIso_of_le {X : Scheme.{u}} {M : X.Modules}
    (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) {U : X.Opens} (hU : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    IsIso (s.app U) := by
  have : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le hU s
  have : IsIso (s.over U) := (AlgebraicGeometry.Quotients.FiniteDescent.OverSection.Construction.OverSectionLocus.isIso_over_iff s U).mpr inferInstance
  have hm : IsIso ((s.over U).val.app (.op (Over.mk (𝟙 U)))) :=
    (SheafOfModules.evaluation (X.ringCatSheaf.over U) (.op (Over.mk (𝟙 U)))).map_isIso (s.over U)
  exact @Functor.map_isIso _ _ _ _ _ _ (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat)
    (s.val.app (.op U)) hm

def sectionAppLinearEquiv {X : Scheme.{u}} {M : X.Modules}
    (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) {U : X.Opens} (hU : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    Γ(X, U) ≃ₗ[Γ(X, U)] Γ(M, U) := by
  have : IsIso (s.app U) := section_app_isIso_of_le s hU
  exact LinearEquiv.ofBijective
    { toFun := s.app U, map_add' := (s.app U).hom.map_add,
      map_smul' := fun r m => s.app_smul r m }
    (ConcreteCategory.bijective_of_isIso (s.app U))

theorem sectionAppLinearEquiv_symm_restrict {X : Scheme.{u}} {M : X.Modules}
    (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) {U V : X.Opens} (h : V ≤ U)
    (hU : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) (m : Γ(M, U)) :
    X.presheaf.map (homOfLE h).op ((sectionAppLinearEquiv s hU).symm m) =
      (sectionAppLinearEquiv s (h.trans hU)).symm (M.presheaf.map (homOfLE h).op m) := by
  apply (sectionAppLinearEquiv s (h.trans hU)).injective
  have hn := PresheafOfModules.naturality_apply s.val (homOfLE h).op
    ((sectionAppLinearEquiv s hU).symm m)
  have hu : s.app U ((sectionAppLinearEquiv s hU).symm m) = m :=
    (sectionAppLinearEquiv s hU).apply_symm_apply m
  have hv : s.app V ((sectionAppLinearEquiv s (h.trans hU)).symm
      (M.presheaf.map (homOfLE h).op m)) = M.presheaf.map (homOfLE h).op m :=
    (sectionAppLinearEquiv s (h.trans hU)).apply_symm_apply _
  exact (hn.trans (congrArg (fun z : Γ(M, U) => M.presheaf.map (homOfLE h).op z) hu)).trans hv.symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionFrameApps.Construction
