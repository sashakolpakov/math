import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.LocalSections
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.LocalResolutionLifts

/-! # Transition Cech Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original local-lift transitions as actual literal-intersection Cech cocycles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
  (hS : S.ShortExact) {t : S.X₃.obj.obj (op (⊤ : Opens X))}
  (l : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g t)

def Sheaf.CohomologyLifts.SheafLocalLiftCover.transitionCech : Abelian.CechCoordinates.AbelianCechCochain S.X₁.obj l.domain 1 :=
  fun a => Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₁
    (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 1))
    (l.transition hS (a 0) (a 1))

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.transitionCech_map :
    Abelian.CechClasses.abelianCechCoefficient (X := X) l.domain S.f.hom 1 (l.transitionCech hS) =
      Abelian.CechCoordinates.abelianCechDelta S.X₂.obj l.domain 0 (Cech.LocalSections.abelianCechLocalSections l.domain S.X₂ l.section_) := by
  funext a
  change S.f.hom.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain a))
    (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₁ _ (l.transition hS (a 0) (a 1))) = _
  rw [Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict, l.transition_map hS]
  change Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ _
    (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_right (l.section_ (a 1)) -
      Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_left (l.section_ (a 0))) = _
  rw [map_sub, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp,
    Cech.LocalSections.abelianCechLocalSections_delta]

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.transitionCech_closed :
    Abelian.CechCoordinates.abelianCechDelta S.X₁.obj l.domain 1 (l.transitionCech hS) = 0 := by
  have : Mono S.f := hS.mono_f
  apply Cech.LocalSections.abelianCechCoefficient_injective l.domain S.f 2
  rw [Abelian.CechClasses.abelianCechCoefficient_delta, l.transitionCech_map hS, Cech.LocalSections.abelianCechDelta_delta]
  funext a
  exact (map_zero (S.f.hom.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain a))).hom).symm

variable (R : InjectiveResolution S.X₁)

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.transitionCech_resolution :
    Abelian.CechClasses.abelianCechCoefficient (X := X) l.domain (R.ι.f 0).hom 1 (l.transitionCech hS) =
      Abelian.CechCoordinates.abelianCechDelta (R.cocomplex.X 0).obj l.domain 0
        (Cech.LocalSections.abelianCechLocalSections l.domain (R.cocomplex.X 0) (l.resolutionLift hS R)) := by
  funext a
  change (R.ι.f 0).hom.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain a))
    (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₁ _ (l.transition hS (a 0) (a 1))) = _
  have h := Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict (F := S.X₁) (G := R.cocomplex.X 0) (R.ι.f 0)
    (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 1))
    (l.transition hS (a 0) (a 1))
  refine h.trans ?_
  refine (congrArg (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 0)
    (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 1)))
    (l.resolutionLift_transition hS R (a 0) (a 1))).trans ?_
  rw [map_sub, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp,
    Cech.LocalSections.abelianCechLocalSections_delta]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
