import OAI.AlgebraicGeometry.DivisorClass.Chern.ResolutionLiftIndependence
import OAI.AlgebraicGeometry.DivisorClass.Chern.TwoStepExt
import OAI.AlgebraicGeometry.DivisorClass.Chern.SecondQuotientCocycles

/-! # Resolution Quotient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ResolutionQuotient

noncomputable section

/-! The quotient connecting class equals the actual resolution cocycle class, with its proved sign. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] {Y : C}

def resolutionZeroSequence (R : InjectiveResolution Y) : ShortComplex C :=
  ShortComplex.mk (R.ι.f 0) (R.cocomplex.d 0 1) R.ι_f_zero_comp_complex_d

theorem resolutionZeroSequence_exact (R : InjectiveResolution Y) : (resolutionZeroSequence R).Exact :=
  ShortComplex.exact_of_f_is_kernel _ R.isLimitKernelFork

instance resolutionZeroSequence_mono (R : InjectiveResolution Y) : Mono (resolutionZeroSequence R).f := by
  change Mono (R.ι.f 0)
  infer_instance

def resolutionSecondQuotientMap (R : InjectiveResolution Y) :
    cokernel (TwoStepQuotient.firstQuotientDifferential (resolutionZeroSequence R)) ⟶ R.cocomplex.X 2 :=
  TwoStepQuotient.secondQuotientDifferential (resolutionZeroSequence R) (R.cocomplex.d 1 2) (R.cocomplex.d_comp_d 0 1 2)

theorem resolutionSecondQuotientMap_closed (R : InjectiveResolution Y) :
    resolutionSecondQuotientMap R ≫ R.cocomplex.d 2 3 = 0 :=
  SecondQuotientCocycles.secondQuotientDifferential_next (resolutionZeroSequence R) (R.cocomplex.d 1 2)
    (R.cocomplex.d_comp_d 0 1 2) (R.cocomplex.d 2 3) (R.cocomplex.d_comp_d 1 2 3)

variable [HasExt.{v} C]

theorem resolutionZeroSequence_twoStepExtClass (R : InjectiveResolution Y) :
    TwoStepExt.twoStepQuotientExtClass (resolutionZeroSequence R) (resolutionZeroSequence_exact R) =
      -R.extMk (resolutionSecondQuotientMap R) 3 rfl (resolutionSecondQuotientMap_closed R) := by
  let S := resolutionZeroSequence R
  have hclosed : TwoStepQuotient.firstQuotientDifferential S ≫ R.cocomplex.d 1 2 = 0 :=
    TwoStepQuotient.firstQuotientDifferential_next S (R.cocomplex.d 1 2) (R.cocomplex.d_comp_d 0 1 2)
  have h₀ := ResolutionLiftIndependence.connectingExtClass_eq_neg_of_lift (TwoStepQuotient.firstQuotientSequence_shortExact S) R
    (𝟙 (R.cocomplex.X 0)) (Category.comp_id _) (TwoStepQuotient.firstQuotientDifferential S)
    ((TwoStepQuotient.firstQuotientDifferential_comp S).trans (Category.id_comp _).symm) hclosed
  have h₁ := ResolutionLiftIndependence.connectingExt_comp_eq_of_lift (TwoStepQuotient.secondQuotientSequence_shortExact S (resolutionZeroSequence_exact R)) R
    (TwoStepQuotient.firstQuotientDifferential S) hclosed (𝟙 (R.cocomplex.X 1)) (Category.comp_id _)
    (resolutionSecondQuotientMap R)
    ((TwoStepQuotient.secondQuotientDifferential_comp S (R.cocomplex.d 1 2) (R.cocomplex.d_comp_d 0 1 2)).trans
      (Category.id_comp _).symm) (resolutionSecondQuotientMap_closed R)
  change (TwoStepQuotient.secondQuotientSequence_shortExact S (resolutionZeroSequence_exact R)).extClass.comp
    (TwoStepQuotient.firstQuotientSequence_shortExact S).extClass (rfl : 1 + 1 = 2) = _
  rw [h₀, Ext.comp_neg, h₁]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ResolutionQuotient
