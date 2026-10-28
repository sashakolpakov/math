import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingExtDegreeTwo

/-! # Resolution Lift Independence -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ResolutionLiftIndependence

noncomputable section

/-! Actual changes of lifts differ by a proved resolution boundary. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.CategoryTheory.Abelian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem shortExact_lift_difference_boundary {S : ShortComplex C} (hS : S.ShortExact)
    {B D : C} (d : B ⟶ D) (m m' : S.X₂ ⟶ B) (hm : S.f ≫ m = S.f ≫ m')
    (q q' : S.X₃ ⟶ D) (hq : S.g ≫ q = m ≫ d) (hq' : S.g ≫ q' = m' ≫ d) :
    ∃ b : S.X₃ ⟶ B, b ≫ d = q - q' := by
  have := hS.epi_g
  let b := hS.exact.desc (m - m') (by rw [comp_sub, hm, sub_self])
  refine ⟨b, ?_⟩
  apply (cancel_epi S.g).mp
  rw [← Category.assoc, hS.exact.g_desc, sub_comp, comp_sub, hq, hq']

variable [HasExt.{w} C]

theorem resolution_extMk_eq_of_boundary {X Y : C} (R : InjectiveResolution Y) (n : ℕ)
    (f g : X ⟶ R.cocomplex.X (n + 1))
    (hf : f ≫ R.cocomplex.d (n + 1) (n + 2) = 0)
    (hg : g ≫ R.cocomplex.d (n + 1) (n + 2) = 0)
    (hb : ∃ b : X ⟶ R.cocomplex.X n, b ≫ R.cocomplex.d n (n + 1) = f - g) :
    R.extMk f (n + 2) rfl hf = R.extMk g (n + 2) rfl hg := by
  apply sub_eq_zero.mp
  rw [R.sub_extMk]
  exact (R.extMk_eq_zero_iff _ _ rfl _ n rfl).mpr hb

theorem connectingExtClass_eq_neg_of_lift {S : ShortComplex C} (hS : S.ShortExact)
    (R : InjectiveResolution S.X₁) (m : S.X₂ ⟶ R.cocomplex.X 0)
    (hm : S.f ≫ m = R.ι.f 0) (q : S.X₃ ⟶ R.cocomplex.X 1)
    (hq : S.g ≫ q = m ≫ R.cocomplex.d 0 1) (hclosed : q ≫ R.cocomplex.d 1 2 = 0) :
    hS.extClass = -R.extMk q 2 rfl hclosed := by
  let := HasDerivedCategory.standard C
  have heq := resolution_extMk_eq_of_boundary R 0 q (ConnectingResolutionCocycle.connectingResolutionQuotient hS R)
    hclosed (ConnectingResolutionCocycle.connectingResolutionQuotient_closed hS R)
    (shortExact_lift_difference_boundary hS (R.cocomplex.d 0 1) m (ConnectingResolutionCocycle.connectingResolutionMiddle hS R)
      (hm.trans (ConnectingResolutionCocycle.connectingResolutionMiddle_comm hS R).symm) q (ConnectingResolutionCocycle.connectingResolutionQuotient hS R)
      hq (ConnectingResolutionCocycle.connectingResolutionQuotient_comm hS R))
  rw [ConnectingExt.connectingExtClass_eq_neg_resolution hS R, ← heq]

theorem connectingExt_comp_eq_of_lift {S : ShortComplex C} (hS : S.ShortExact)
    {Y : C} (R : InjectiveResolution Y) (f : S.X₁ ⟶ R.cocomplex.X 1)
    (hf : f ≫ R.cocomplex.d 1 2 = 0) (m : S.X₂ ⟶ R.cocomplex.X 1)
    (hm : S.f ≫ m = f) (q : S.X₃ ⟶ R.cocomplex.X 2)
    (hq : S.g ≫ q = m ≫ R.cocomplex.d 1 2) (hclosed : q ≫ R.cocomplex.d 2 3 = 0) :
    hS.extClass.comp (R.extMk f 2 rfl hf) (rfl : 1 + 1 = 2) = R.extMk q 3 rfl hclosed := by
  let := HasDerivedCategory.standard C
  have heq := resolution_extMk_eq_of_boundary R 1 q (ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf)
    hclosed (ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient_closed hS R f hf)
    (shortExact_lift_difference_boundary hS (R.cocomplex.d 1 2) m (ConnectingResolutionDegreeTwo.connectingResolutionOneMiddle hS R f)
      (hm.trans (ConnectingResolutionDegreeTwo.connectingResolutionOneMiddle_comm hS R f).symm) q (ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf)
      hq (ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient_comm hS R f hf))
  rw [ConnectingExtDegreeTwo.connectingExt_comp_resolutionOne hS R f hf, ← heq]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ResolutionLiftIndependence
