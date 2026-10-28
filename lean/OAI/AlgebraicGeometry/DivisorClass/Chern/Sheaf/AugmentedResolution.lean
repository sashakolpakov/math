import OAI.AlgebraicGeometry.DivisorClass.Chern.AugmentedResolutionComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionQuotientBoundary

/-! # Augmented Resolution -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.AugmentedResolution

noncomputable section

/-! The two-step boundary of an actual augmented cochain complex is its mapped resolution class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

theorem sheafCochainMap_section_closed
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ} (r : K ⟶ L) (n : ℕ)
    (t : (K.X n).obj.obj (op (⊤ : Opens X)))
    (ht : (K.d n (n + 1)).hom.app (op (⊤ : Opens X)) t = 0) :
    (L.d n (n + 1)).hom.app (op (⊤ : Opens X)) ((r.f n).hom.app (op (⊤ : Opens X)) t) = 0 := by
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op (⊤ : Opens X))) (r.comm n (n + 1))) t
  change (L.d n (n + 1)).hom.app (op (⊤ : Opens X)) ((r.f n).hom.app (op (⊤ : Opens X)) t) =
    (r.f (n + 1)).hom.app (op (⊤ : Opens X)) ((K.d n (n + 1)).hom.app (op (⊤ : Opens X)) t) at hc
  exact hc.trans (by rw [ht, map_zero])

theorem sheafTwoStepBoundary_cochain_resolution
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    {F Y : TopCat.Sheaf AddCommGrpCat.{0} X} (i : F ⟶ K.X 0) (hi : i ≫ K.d 0 1 = 0)
    (hK : (AugmentedResolutionComparison.augmentedZeroSequence K i hi).Exact) [Mono i]
    (R : InjectiveResolution Y) (u : F ⟶ Y) (r : K ⟶ R.cocomplex)
    (hr : i ≫ r.f 0 = u ≫ R.ι.f 0)
    (s : (cokernel (TwoStepQuotient.firstQuotientDifferential (AugmentedResolutionComparison.augmentedZeroSequence K i hi))).obj.obj (op (⊤ : Opens X)))
    (t : (K.X 2).obj.obj (op (⊤ : Opens X)))
    (ht : (K.d 2 3).hom.app (op (⊤ : Opens X)) t = 0)
    (hs : (TwoStepQuotient.secondQuotientDifferential (AugmentedResolutionComparison.augmentedZeroSequence K i hi) (K.d 1 2)
      (K.d_comp_d 0 1 2)).hom.app (op (⊤ : Opens X)) s = t) :
    CategoryTheory.Sheaf.H.map u 2 (TwoStepBoundary.sheafTwoStepBoundary (AugmentedResolutionComparison.augmentedZeroSequence K i hi) hK s) =
      -ResolutionClasses.sheafResolutionCycleClass R 2 ((r.f 2).hom.app (op (⊤ : Opens X)) t)
        (sheafCochainMap_section_closed r 2 t ht) := by
  let φ := AugmentedResolutionComparison.augmentedResolutionZeroComparison K i hi R u r hr
  have hm := TwoStepBoundary.sheafTwoStepBoundary_naturality hK (ResolutionQuotient.resolutionZeroSequence_exact R) φ s
  have hb := ResolutionQuotientBoundary.sheafTwoStepBoundary_resolution R ((TwoStepQuotientNaturality.secondQuotientMap φ).hom.app (op (⊤ : Opens X)) s)
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op (⊤ : Opens X)))
      (AugmentedResolutionComparison.augmentedResolutionSecondQuotient_comp K i hi R u r hr)) s
  change ResolutionQuotientBoundary.resolutionSecondQuotientSection R ((TwoStepQuotientNaturality.secondQuotientMap φ).hom.app (op (⊤ : Opens X)) s) =
    (r.f 2).hom.app (op (⊤ : Opens X))
      ((TwoStepQuotient.secondQuotientDifferential (AugmentedResolutionComparison.augmentedZeroSequence K i hi) (K.d 1 2)
        (K.d_comp_d 0 1 2)).hom.app (op (⊤ : Opens X)) s) at hc
  rw [hs] at hc
  have hclass : ResolutionClasses.sheafResolutionCycleClass R 2
      (ResolutionQuotientBoundary.resolutionSecondQuotientSection R ((TwoStepQuotientNaturality.secondQuotientMap φ).hom.app (op (⊤ : Opens X)) s))
      (ResolutionQuotientBoundary.resolutionSecondQuotientSection_closed R _) =
        ResolutionClasses.sheafResolutionCycleClass R 2 ((r.f 2).hom.app (op (⊤ : Opens X)) t)
          (sheafCochainMap_section_closed r 2 t ht) := by
    congr 1
  exact hm.trans (hb.trans (congrArg Neg.neg hclass))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.AugmentedResolution
