import OAI.AlgebraicGeometry.DivisorClass.Chern.ResolutionQuotient

/-! # Augmented Resolution Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.AugmentedResolutionComparison

noncomputable section

/-! A genuine augmented cochain map induces the actual first two quotient maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

def augmentedZeroSequence (K : CochainComplex C ℕ) {F : C}
    (i : F ⟶ K.X 0) (hi : i ≫ K.d 0 1 = 0) : ShortComplex C := ShortComplex.mk i (K.d 0 1) hi

instance augmentedZeroSequence_mono (K : CochainComplex C ℕ) {F : C}
    (i : F ⟶ K.X 0) (hi : i ≫ K.d 0 1 = 0) [Mono i] : Mono (augmentedZeroSequence K i hi).f := by
  change Mono i
  infer_instance

def augmentedResolutionZeroComparison (K : CochainComplex C ℕ) {F Y : C}
    (i : F ⟶ K.X 0) (hi : i ≫ K.d 0 1 = 0) (R : InjectiveResolution Y)
    (u : F ⟶ Y) (r : K ⟶ R.cocomplex) (hr : i ≫ r.f 0 = u ≫ R.ι.f 0) :
    augmentedZeroSequence K i hi ⟶ ResolutionQuotient.resolutionZeroSequence R where
  τ₁ := u
  τ₂ := r.f 0
  τ₃ := r.f 1
  comm₁₂ := hr.symm
  comm₂₃ := r.comm 0 1

theorem augmentedResolutionSecondQuotient_comp (K : CochainComplex C ℕ) {F Y : C}
    (i : F ⟶ K.X 0) (hi : i ≫ K.d 0 1 = 0) (R : InjectiveResolution Y)
    (u : F ⟶ Y) (r : K ⟶ R.cocomplex) (hr : i ≫ r.f 0 = u ≫ R.ι.f 0) :
    TwoStepQuotientNaturality.secondQuotientMap (augmentedResolutionZeroComparison K i hi R u r hr) ≫ ResolutionQuotient.resolutionSecondQuotientMap R =
      TwoStepQuotient.secondQuotientDifferential (augmentedZeroSequence K i hi) (K.d 1 2) (K.d_comp_d 0 1 2) ≫ r.f 2 :=
  TwoStepQuotientNaturality.secondQuotientMap_differential (augmentedResolutionZeroComparison K i hi R u r hr)
    (K.d 1 2) (K.d_comp_d 0 1 2) (R.cocomplex.d 1 2) (R.cocomplex.d_comp_d 0 1 2)
    (r.f 2) (r.comm 1 2).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.AugmentedResolutionComparison
