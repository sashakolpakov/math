import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TwoStepBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle

/-! # Two Step Local Vanishing -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TwoStepLocalVanishing

noncomputable section

/-! Actual local representatives detect vanishing of the quotient connecting class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}

theorem secondQuotientMap_section_eq_zero (φ : S ⟶ T)
    {B : TopCat.Sheaf AddCommGrpCat.{0} X} (d : T.X₃ ⟶ B) (hd : T.g ≫ d = 0)
    (hnext : (ShortComplex.mk T.g d hd).Exact)
    (s : (cokernel (TwoStepQuotient.firstQuotientDifferential S)).obj.obj (op (⊤ : Opens X)))
    (hlift : ∀ (U : Opens X) (a : S.X₃.obj.obj (op U)),
      (cokernel.π (TwoStepQuotient.firstQuotientDifferential S)).hom.app (op U) a =
        TransitionCocycle.sheafSectionRestrict _ le_top s → d.hom.app (op U) (φ.τ₃.hom.app (op U) a) = 0) :
    (TwoStepQuotientNaturality.secondQuotientMap φ).hom.app (op (⊤ : Opens X)) s = 0 := by
  let l := CohomologyLifts.sheafLocalLiftCover (cokernel.π (TwoStepQuotient.firstQuotientDifferential S)) s
  have hmono : Mono (TwoStepQuotient.secondQuotientDifferential T d hd) := TwoStepQuotient.secondQuotientDifferential_mono T d hd hnext
  apply (cokernel (TwoStepQuotient.firstQuotientDifferential T)).eq_of_locally_eq' l.domain ⊤
    (fun _ => homOfLE le_top) (by rw [l.iSup_domain])
  intro i
  change TransitionCocycle.sheafSectionRestrict _ le_top ((TwoStepQuotientNaturality.secondQuotientMap φ).hom.app (op (⊤ : Opens X)) s) =
    TransitionCocycle.sheafSectionRestrict _ le_top 0
  have hli : (cokernel.π (TwoStepQuotient.firstQuotientDifferential S)).hom.app (op (l.domain i)) (l.section_ i) =
      TransitionCocycle.sheafSectionRestrict _ le_top s := l.image i
  rw [map_zero, ← TransitionCocycle.sheafSectionMap_restrict, ← hli]
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op (l.domain i))) (TwoStepQuotientNaturality.secondQuotientMap_comp φ)) (l.section_ i)
  change (TwoStepQuotientNaturality.secondQuotientMap φ).hom.app (op (l.domain i))
    ((cokernel.π (TwoStepQuotient.firstQuotientDifferential S)).hom.app (op (l.domain i)) (l.section_ i)) =
      (cokernel.π (TwoStepQuotient.firstQuotientDifferential T)).hom.app (op (l.domain i))
        (φ.τ₃.hom.app (op (l.domain i)) (l.section_ i)) at hc
  rw [hc]
  apply TransitionCocycle.sheafMono_section_injective (TwoStepQuotient.secondQuotientDifferential T d hd) (l.domain i)
  rw [map_zero]
  have ht := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op (l.domain i))) (TwoStepQuotient.secondQuotientDifferential_comp T d hd))
      (φ.τ₃.hom.app (op (l.domain i)) (l.section_ i))
  exact ht.trans (hlift (l.domain i) (l.section_ i) hli)

theorem sheafTwoStepBoundary_vanishes_of_local_lifts
    (hS : S.Exact) (hT : T.Exact) [Mono S.f] [Mono T.f] (φ : S ⟶ T)
    {B : TopCat.Sheaf AddCommGrpCat.{0} X} (d : T.X₃ ⟶ B) (hd : T.g ≫ d = 0)
    (hnext : (ShortComplex.mk T.g d hd).Exact)
    (s : (cokernel (TwoStepQuotient.firstQuotientDifferential S)).obj.obj (op (⊤ : Opens X)))
    (hlift : ∀ (U : Opens X) (a : S.X₃.obj.obj (op U)),
      (cokernel.π (TwoStepQuotient.firstQuotientDifferential S)).hom.app (op U) a =
        TransitionCocycle.sheafSectionRestrict _ le_top s → d.hom.app (op U) (φ.τ₃.hom.app (op U) a) = 0) :
    CategoryTheory.Sheaf.H.map φ.τ₁ 2 (TwoStepBoundary.sheafTwoStepBoundary S hS s) = 0 :=
  TwoStepBoundary.sheafTwoStepBoundary_image_eq_zero hS hT φ s
    (secondQuotientMap_section_eq_zero φ d hd hnext s hlift)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TwoStepLocalVanishing
