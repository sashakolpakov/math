import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # De Rham Semilinear Left -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearLeft.DeRhamSemilinearEquiv

noncomputable section

/-! # Ring equivalences give actual semilinear equivalences of de Rham complexes -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] (σ : R ≃+* S) (f : A ≃+* B)
  (h : ∀ r, f (algebraMap R A r) = algebraMap S B (σ r))

local instance forwardScalarInverse : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ

local instance backwardScalarInverse : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.symm σ.toRingHom σ.symm.toRingHom

include h in
theorem inverse_compatibility (s : S) :
    f.symm (algebraMap S B s) = algebraMap R A (σ.symm s) := by
  apply f.injective
  rw [RingEquiv.apply_symm_apply, h, RingEquiv.apply_symm_apply]

def forward (n : ℕ) : DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₛₗ[σ.toRingHom] DeRhamPresentationTo.DeRhamPresentation.Form S B n :=
  DeRhamSemilinearA.DeRhamSemilinearMap.formMap R S A B σ.toRingHom f.toRingHom h n

def backward (n : ℕ) : DeRhamPresentationTo.DeRhamPresentation.Form S B n →ₛₗ[σ.symm.toRingHom] DeRhamPresentationTo.DeRhamPresentation.Form R A n :=
  DeRhamSemilinearA.DeRhamSemilinearMap.formMap S R B A σ.symm.toRingHom f.symm.toRingHom
    (inverse_compatibility R S A B σ f h) n

theorem forward_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    forward R S A B σ f h n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = DeRhamPresentationTo.DeRhamPresentation.symbol S B (f a) (f ∘ v) :=
  DeRhamSemilinearA.DeRhamSemilinearMap.formMap_symbol R S A B σ.toRingHom f.toRingHom h n a v

theorem backward_symbol (n : ℕ) (a : B) (v : Fin n → B) :
    backward R S A B σ f h n (DeRhamPresentationTo.DeRhamPresentation.symbol S B a v) = DeRhamPresentationTo.DeRhamPresentation.symbol R A (f.symm a) (f.symm ∘ v) :=
  DeRhamSemilinearA.DeRhamSemilinearMap.formMap_symbol S R B A σ.symm.toRingHom f.symm.toRingHom
    (inverse_compatibility R S A B σ f h) n a v

theorem left_inverse (n : ℕ) : Function.LeftInverse
    (backward R S A B σ f h n) (forward R S A B σ f h n) := by
  have he : (backward R S A B σ f h n).toAddMonoidHom.comp
      (forward R S A B σ f h n).toAddMonoidHom = AddMonoidHom.id (DeRhamPresentationTo.DeRhamPresentation.Form R A n) := by
    apply DeRhamSemilinearA.DeRhamSemilinearMap.addHom_ext R A n
    intro a v
    change backward R S A B σ f h n (forward R S A B σ f h n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = DeRhamPresentationTo.DeRhamPresentation.symbol R A a v
    rw [forward_symbol, backward_symbol, RingEquiv.symm_apply_apply]
    congr 1
    funext i
    exact f.symm_apply_apply (v i)
  intro ω
  exact DFunLike.congr_fun he ω

theorem right_inverse (n : ℕ) : Function.RightInverse
    (backward R S A B σ f h n) (forward R S A B σ f h n) := by
  have he : (forward R S A B σ f h n).toAddMonoidHom.comp
      (backward R S A B σ f h n).toAddMonoidHom = AddMonoidHom.id (DeRhamPresentationTo.DeRhamPresentation.Form S B n) := by
    apply DeRhamSemilinearA.DeRhamSemilinearMap.addHom_ext S B n
    intro a v
    change forward R S A B σ f h n (backward R S A B σ f h n (DeRhamPresentationTo.DeRhamPresentation.symbol S B a v)) = DeRhamPresentationTo.DeRhamPresentation.symbol S B a v
    rw [backward_symbol, forward_symbol, RingEquiv.apply_symm_apply]
    congr 1
    funext i
    exact f.apply_symm_apply (v i)
  intro ω
  exact DFunLike.congr_fun he ω

def formsEquiv (n : ℕ) : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) (DeRhamPresentationTo.DeRhamPresentation.Form R A n) (DeRhamPresentationTo.DeRhamPresentation.Form S B n) :=
  LinearEquiv.ofBijective (forward R S A B σ f h n)
    ⟨(left_inverse R S A B σ f h n).injective, (right_inverse R S A B σ f h n).surjective⟩

def linearMap : DeRhamPresentationTo.DeRhamPresentation.complex R A ⟶
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex σ.toRingHom (DeRhamPresentationTo.DeRhamPresentation.complex S B) :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap
    (DeRhamSemilinearA.DeRhamSemilinearMap.complexMap R S A B σ.toRingHom f.toRingHom h)

instance component_isIso (n : ℕ) : IsIso ((linearMap R S A B σ f h).f n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (formsEquiv R S A B σ f h n).bijective

instance linearMap_isIso : IsIso (linearMap R S A B σ f h) := by
  exact HomologicalComplex.Hom.isIso_of_components _

def complexIso : DeRhamPresentationTo.DeRhamPresentation.complex R A ≅
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex σ.toRingHom (DeRhamPresentationTo.DeRhamPresentation.complex S B) :=
  asIso (linearMap R S A B σ f h)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearLeft.DeRhamSemilinearEquiv
