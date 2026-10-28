import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ConcretePolarizedPeriodModel
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PositivePeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LinearIntegralAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RiemannAdjoints
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ComplexFibers
import OAI.RepresentationTheory.Theta.Geometric.LinePeriodPairing
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual

/-! # Theta Construction Integral Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ThetaConstructionIntegralAction

noncomputable section

/-! An action preserving a positive marked torus algebraizes on its
actual ThetaConstruction model. Adjointness for the retained Riemann form implies the
original algebraic Rosati equation for the constructed primitive dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LinearIntegralAction.IntrinsicLinearMaps

variable {g : ℕ} {J : Picard.ThetaConstruction.DefinitionsIntegral.IntegralMatrix g} {T : Picard.ThetaConstruction.DefinitionsIntegral.MarkedPolarizedTorus g J}
    (M : Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel T)

attribute [local implicit_reducible] Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.abelianScheme
  Picard.ThetaConstruction.IntegralDualModel.Geometric.IntegralDualAlgebraicModel.abelianScheme
  Picard.ThetaConstruction.ProjectivePeriodData.Geometric.projectivePeriodData RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.ofCompactProjectiveTorus
  Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.toOver

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

section Action

variable {R : Type*} [CommRing R]
    (ρ : R →+* Module.End ℂ (Picard.ThetaConstruction.DefinitionsIntegral.Tangent g))
    (hρ : ∀ a x, x ∈ T.lattice → ρ a x ∈ T.lattice)

def linearAction : R →+* Module.End ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) :=
  M.periodDifferential.toLinearEquiv.conjRingEquiv.toRingHom.comp ρ

theorem linearAction_apply (a : R) (x : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) :
    linearAction M ρ a x = M.periodDifferential (ρ a (M.periodDifferential.symm x)) := rfl

include hρ in
theorem linearAction_preserves (a : R) (x : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
    (hx : x ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian) : linearAction M ρ a x ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian := by
  have hi (y : Picard.ThetaConstruction.DefinitionsIntegral.Tangent g) : M.periodDifferential y ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M.abelian ↔ y ∈ T.lattice :=
    M.periodDifferential_lattice_iff y
  rw [linearAction_apply, hi]
  apply hρ a
  rw [← hi, M.periodDifferential.apply_symm_apply]
  exact hx

def integralAction : ActionData.IntegralAction R M.abelianScheme := by
  let a := Intrinsic.LinearIntegralAction.IntrinsicLinearMaps.integralActionOfNativeLinear M.abelian (linearAction M ρ)
    (linearAction_preserves M ρ hρ)
  exact {
    map := a.map
    preservesGroup := a.preservesGroup
    map_zero := a.map_zero
    map_one := a.map_one
    map_add := a.map_add
    map_mul := a.map_mul }

theorem integralAction_lift (a : R) :
    Intrinsic.Maps.IntrinsicLinearMaps.linearLift ((integralAction M ρ hρ).map a) = linearAction M ρ a := by
  exact Intrinsic.LinearIntegralAction.IntrinsicLinearMaps.integralActionOfNativeLinear_lift M.abelian (linearAction M ρ)
    (linearAction_preserves M ρ hρ) a

theorem integralAction_lift_apply (a : R) (x : Picard.ThetaConstruction.DefinitionsIntegral.Tangent g) :
    Intrinsic.Maps.IntrinsicLinearMaps.linearLift ((integralAction M ρ hρ).map a) (M.periodDifferential x) =
      M.periodDifferential (ρ a x) := by
  rw [integralAction_lift, linearAction_apply, M.periodDifferential.symm_apply_apply]

end Action

variable {D : Picard.ThetaConstruction.IntegralDualModel.Geometric.IntegralDualAlgebraicModel T} {p : Picard.ThetaConstruction.IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M D}
    (C : Picard.ThetaConstruction.PrimitiveDual.Geometric.PrimitiveDualConstruction p)

local instance : IsIntegral D.abelian.toOver.left := D.abelian.variety.property
local instance : Smooth D.abelian.toOver.hom := D.abelian.variety.presentation.smooth
local instance : IsIntegral (D.abelian.toOver ⊗ D.abelian.toOver).left :=
  (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety D.abelian.variety D.abelian.variety).property
local instance : IsIntegral (C.dual.abelian.scheme ⊗ C.dual.abelian.scheme).left :=
  inferInstanceAs (IsIntegral (D.abelian.toOver ⊗ D.abelian.toOver).left)
local instance : IsMonHom (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom) :=
  p.isogeny.preservesGroup
local instance : IsFinite (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom).left :=
  p.isogeny.finite

theorem primitive_riemann (x y : Picard.ThetaConstruction.DefinitionsIntegral.Tangent g) :
    Intrinsic.RiemannForm.nativeRiemannForm M.abelian C.ampleLine C.ample
      (M.periodDifferential x) (M.periodDifferential y) = T.riemannForm x y := by
  let H := Intrinsic.RiemannForm.nativeRiemannForm M.abelian C.ampleLine C.ample
  have hp (z : Picard.ThetaConstruction.DefinitionsIntegral.CVec g) : M.periodDifferential (T.periodMap z) =
      ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap M.markedNativeBasis z :=
    (LinearMap.congr_fun M.markedNativeBasis_periodMap z).symm
  have him (v w : Picard.ThetaConstruction.DefinitionsIntegral.Tangent g) : (H (M.periodDifferential v) (M.periodDifferential w)).im =
      (T.riemannForm v w).im := by
    obtain ⟨a, rfl⟩ := T.real_marking.surjective v
    obtain ⟨b, rfl⟩ := T.real_marking.surjective w
    rw [hp, hp]
    exact (Picard.ThetaConstruction.IntrinsicPolarization.Geometric.native_polarization_marking M.abelian C.ampleLine C.ample M.markedNativeBasis J
      (M.markedNativeBasis_polarization C.ampleLine C.ample C.chern) a b).trans
        (T.polarization_marking a b).symm
  apply Complex.ext
  · have h := him x (Complex.I • y)
    have hI : M.periodDifferential (Complex.I • y) = Complex.I • M.periodDifferential y :=
      M.periodDifferential.map_smul Complex.I y
    have hleft : H (M.periodDifferential x) (M.periodDifferential (Complex.I • y)) =
        Complex.I * H (M.periodDifferential x) (M.periodDifferential y) :=
      (congrArg (H (M.periodDifferential x)) hI).trans
        ((H (M.periodDifferential x)).map_smul Complex.I (M.periodDifferential y))
    have hright : T.riemannForm x (Complex.I • y) = Complex.I * T.riemannForm x y :=
      (T.riemannForm x).map_smul Complex.I y
    have hre := (congrArg Complex.im hleft).symm.trans (h.trans (congrArg Complex.im hright))
    simpa only [Complex.I_mul_im] using hre
  · exact him x y

theorem primitive_chern_eq_polarization (I : Picard.ThetaConstruction.PolarizationTypeData.Geometric.IntegralPolarizationType J) {N : ℕ}
    (β : M.abelianScheme.FullLevel N) :
    Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine = Intrinsic.ChernPairing.nativePolarizationForm (C.polarized I β) := by
  let Q := C.poincare.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left
  exact Polarization.HomologyForm.nativePolarizationForm_of_witness (C.polarized I β) C.ampleLine Q rfl
    (RepresentationTheory.Theta.Geometric.QuotientDifferenceFibers.quotientDifference_formulaIso p.isogeny C.ampleLine C.poincare C.difference)

def periodPairing : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian →ₗ[ℚ]
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian →ₗ[ℚ] ℚ :=
  RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing D.abelian M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare)

theorem periodPairing_isogeny (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    periodPairing M C (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom) x) y =
      Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y := by
  let f : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom
  have hp := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_pullback M.abelian M.abelian D.abelian M.abelian f
    (𝟙 M.abelian.toOver) (HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) x y
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_id] at hp
  have he := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_biextension M.abelian C.ampleLine
    (C.poincare.pullback (f ⊗ₘ 𝟙 M.abelian.toOver).left)
    (RepresentationTheory.Theta.Geometric.QuotientDifferenceFibers.quotientDifference_formulaIso p.isogeny C.ampleLine C.poincare C.difference)
  exact hp.symm.trans (LinearMap.congr_fun (LinearMap.congr_fun he x) y)

theorem isogeny_period_bijective :
    Function.Bijective (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom)) := by
  let f : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom
  have hd : Module.finrank ℚ (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) =
      Module.finrank ℚ (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian) := by
    rw [Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank, Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank, M.abelian_dimension, D.abelian_dimension]
  exact ((Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f).linearEquivOfInjective (Finite.ComplexFibers.NativeLinearMaps.rationalLift_injective_of_isFinite f) hd).bijective

theorem periodPairing_left_ext (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian)
    (h : ∀ w, periodPairing M C x w = periodPairing M C y w) : x = y := by
  obtain ⟨u, rfl⟩ := (isogeny_period_bijective M (p := p)).surjective x
  obtain ⟨v, rfl⟩ := (isogeny_period_bijective M (p := p)).surjective y
  apply congrArg (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom))
  apply sub_eq_zero.mp
  apply Intrinsic.ChernPeriod.nativeChernForm_separating M.abelian C.ampleLine C.ample
  intro w
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
  exact (periodPairing_isogeny M C u w).symm.trans
    ((h w).trans (periodPairing_isogeny M C v w))

theorem periodPairing_detects (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f v : A.toOver ⟶ D.abelian.toOver) [IsMonHom f] [IsMonHom v]
    (h : ∀ x y, periodPairing M C (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) y =
      periodPairing M C (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift v x) y) : f = v := by
  apply Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful f v
  exact LinearMap.ext (fun x => periodPairing_left_ext M C _ _ (h x))

theorem primitive_polarization_adjoint
    (f v : M.abelian.toOver ⟶ M.abelian.toOver) [IsMonHom f] [IsMonHom v]
    (hv : ∀ x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian,
      Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift v x) y =
        Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y)) :
    p.isogeny.hom ≫ Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback C.dual C.dual f = v ≫ p.isogeny.hom := by
  let d : D.abelian.toOver ⟶ D.abelian.toOver := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback C.dual C.dual f
  let : IsMonHom d := RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual.nativePoincareDual_isMonHom C.dual C.dual f
  have hd := (RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual.nativePoincareDual_pullback_class C.dual C.dual f).symm
  change p.isogeny.hom ≫ d = v ≫ p.isogeny.hom
  apply periodPairing_detects M C M.abelian
  intro x y
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  have ha := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_adjoint D.abelian M.abelian
    (HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) d f hd (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x) y
  change periodPairing M C (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift d (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x)) y =
    periodPairing M C (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift v x)) y
  change periodPairing M C (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift d (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x)) y =
    periodPairing M C (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x) (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) at ha
  rw [ha, periodPairing_isogeny, periodPairing_isogeny]
  exact (hv x y).symm

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (ρ : NumberField.RingOfIntegers E →+* Module.End ℂ (Picard.ThetaConstruction.DefinitionsIntegral.Tangent g))
    (hρ : ∀ a x, x ∈ T.lattice → ρ a x ∈ T.lattice)
    (hadj : ∀ a x y, T.riemannForm (ρ (NumberField.IsCMField.ringOfIntegersComplexConj E a) x) y =
      T.riemannForm x (ρ a y))

include hadj in
theorem action_chern_adjoint (a : NumberField.RingOfIntegers E)
    (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((integralAction M ρ hρ).map
        (NumberField.IsCMField.ringOfIntegersComplexConj E a)) x) y =
      Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((integralAction M ρ hρ).map a) y) := by
  have h (v w : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) :
      Intrinsic.RiemannForm.nativeRiemannForm M.abelian C.ampleLine C.ample
        (Intrinsic.Maps.IntrinsicLinearMaps.linearLift ((integralAction M ρ hρ).map
          (NumberField.IsCMField.ringOfIntegersComplexConj E a)) v) w =
      Intrinsic.RiemannForm.nativeRiemannForm M.abelian C.ampleLine C.ample v
        (Intrinsic.Maps.IntrinsicLinearMaps.linearLift ((integralAction M ρ hρ).map a) w) := by
    obtain ⟨v, rfl⟩ := M.periodDifferential.surjective v
    obtain ⟨w, rfl⟩ := M.periodDifferential.surjective w
    rw [integralAction_lift_apply, integralAction_lift_apply, primitive_riemann, primitive_riemann]
    exact hadj a v w
  have hreal := congrArg Complex.im (h x.val y.val)
  change (Intrinsic.RiemannForm.nativeRiemannForm M.abelian C.ampleLine C.ample
    (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((integralAction M ρ hρ).map
      (NumberField.IsCMField.ringOfIntegersComplexConj E a)) x).val y.val).im =
    (Intrinsic.RiemannForm.nativeRiemannForm M.abelian C.ampleLine C.ample x.val
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((integralAction M ρ hρ).map a) y).val).im at hreal
  rw [Intrinsic.RiemannForm.nativeRiemannForm_period, Intrinsic.RiemannForm.nativeRiemannForm_period] at hreal
  exact_mod_cast hreal

include hadj in
theorem primitive_rosati (I : Picard.ThetaConstruction.PolarizationTypeData.Geometric.IntegralPolarizationType J) {N : ℕ}
    (β : M.abelianScheme.FullLevel N) :
    ActionData.RosatiConjugation (C.polarized I β) (integralAction M ρ hρ) := by
  intro a
  let f := (integralAction M ρ hρ).map a
  refine ⟨Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback C.dual C.dual f,
    RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual.nativePoincareDual_isMonHom C.dual C.dual f,
    (RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual.nativePoincareDual_pullback_class C.dual C.dual f).symm, ?_⟩
  exact primitive_polarization_adjoint M C f
    ((integralAction M ρ hρ).map (NumberField.IsCMField.ringOfIntegersComplexConj E a))
    (action_chern_adjoint M C ρ hρ hadj a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ThetaConstructionIntegralAction
