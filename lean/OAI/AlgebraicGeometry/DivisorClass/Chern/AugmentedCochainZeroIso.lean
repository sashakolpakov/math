import OAI.AlgebraicGeometry.DivisorClass.Chern.AugmentedResolutionComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ResolutionHomotopy

/-! # Augmented Cochain Zero Iso -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.AugmentedCochainZeroIso

noncomputable section

/-! The degree-zero cohomology identification determined by an actual exact augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C : Type*} [Category C] [Abelian C]
  (K : CochainComplex C ℕ) {F : C} (i : F ⟶ K.X 0) (hi : i ≫ K.d 0 1 = 0)
  (hK : (AugmentedResolutionComparison.augmentedZeroSequence K i hi).Exact) [Mono i]

def augmentedCochainZeroIso : F ≅ K.homology 0 :=
  hK.fIsKernel.conePointUniqueUpToIso (K.cyclesIsKernel 0 1 (by simp)) ≪≫ K.isoHomologyπ₀

theorem augmentedCochainZeroIso_augmentation :
    (augmentedCochainZeroIso K i hi hK).hom ≫ (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0 = i := by
  rw [HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_f_zero, augmentedCochainZeroIso, Iso.trans_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

theorem augmentedCochainZeroIso_resolutionLift (he : ∀ n, K.ExactAt (n + 1))
    (R : InjectiveResolution (K.homology 0)) :
    i ≫ (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he R).f 0 = (augmentedCochainZeroIso K i hi hK).hom ≫ R.ι.f 0 := by
  calc
    _ = ((augmentedCochainZeroIso K i hi hK).hom ≫
        (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0) ≫ (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he R).f 0 :=
      congrArg (fun g => g ≫ (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he R).f 0)
        (augmentedCochainZeroIso_augmentation K i hi hK).symm
    _ = _ := by
      rw [Category.assoc]
      exact congrArg (fun g => (augmentedCochainZeroIso K i hi hK).hom ≫ g)
        (congrArg (fun f => f.f 0) (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift_augmentation K he R))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.AugmentedCochainZeroIso
