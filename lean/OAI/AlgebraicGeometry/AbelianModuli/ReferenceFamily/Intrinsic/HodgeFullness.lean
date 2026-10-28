import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LinearDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeLinearMap

/-! # Hodge Fullness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeFullness.IntrinsicLinearMaps

noncomputable section

section

/-! Integral maps of the constructed native rational Hodge structures
are exactly realized by actual algebraic group maps. No algebraization
or comparison property is added to the input Hodge map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeLinearMap.IntrinsicRationalPeriods

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B)
    (hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B) f)
    (hΛ : ∀ v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods A, f v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods B)

def nativeHodgeDescend : A.toOver ⟶ B.toOver :=
  LinearDescent.IntrinsicLinearMaps.nativeLinearDescend (HodgeLinearMap.IntrinsicRationalPeriods.nativeHodgeLinearMap f) (HodgeLinearMap.IntrinsicRationalPeriods.nativeHodgeLinearMap_preserves f hf hΛ)

instance nativeHodgeDescend_isMonHom : IsMonHom (nativeHodgeDescend f hf hΛ) :=
  LinearDescent.IntrinsicLinearMaps.nativeLinearDescend_isMonHom (HodgeLinearMap.IntrinsicRationalPeriods.nativeHodgeLinearMap f) (HodgeLinearMap.IntrinsicRationalPeriods.nativeHodgeLinearMap_preserves f hf hΛ)

theorem rationalLift_nativeHodgeDescend : IntegralMaps.IntrinsicLinearMaps.rationalLift (nativeHodgeDescend f hf hΛ) = f := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact (LinearMap.congr_fun (LinearDescent.IntrinsicLinearMaps.linearLift_nativeLinearDescend
    (HodgeLinearMap.IntrinsicRationalPeriods.nativeHodgeLinearMap f) (HodgeLinearMap.IntrinsicRationalPeriods.nativeHodgeLinearMap_preserves f hf hΛ)) v.val).trans
      (HodgeLinearMap.IntrinsicRationalPeriods.nativeHodgeLinearMap_rational f hf v)

theorem nativeHodgeDescend_unique (g : A.toOver ⟶ B.toOver) [IsMonHom g]
    (hg : IntegralMaps.IntrinsicLinearMaps.rationalLift g = f) : g = nativeHodgeDescend f hf hΛ :=
  IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful g (nativeHodgeDescend f hf hΛ)
    (hg.trans (rationalLift_nativeHodgeDescend f hf hΛ).symm)

end

/-! An isomorphism of the actual integral Hodge period structures
constructs an algebraic group-scheme isomorphism. The inverse and both
composition identities are verified using the faithful period functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeLinearMap.IntrinsicRationalPeriods

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (e : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B)
    (he : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B) e.toLinearMap)
    (hi : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) e.symm.toLinearMap)
    (hΛ : ∀ v, v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods A ↔ e v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods B)

include hΛ in
theorem nativeIntegralHodgeIso_inverse_lattice (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B) (hv : v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods B) :
    e.symm v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods A :=
  (hΛ (e.symm v)).mpr ((congrArg (fun w => w ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods B) (e.apply_symm_apply v)).mpr hv)

def nativeIntegralHodgeIso : A.toOver ≅ B.toOver where
  hom := nativeHodgeDescend e.toLinearMap he (fun v hv => (hΛ v).mp hv)
  inv := nativeHodgeDescend e.symm.toLinearMap hi (nativeIntegralHodgeIso_inverse_lattice e hΛ)
  hom_inv_id := by
    apply IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful
    rw [IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, rationalLift_nativeHodgeDescend, rationalLift_nativeHodgeDescend, IntegralMaps.IntrinsicLinearMaps.rationalLift_id]
    exact LinearMap.ext (fun v => e.symm_apply_apply v)
  inv_hom_id := by
    apply IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful
    rw [IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, rationalLift_nativeHodgeDescend, rationalLift_nativeHodgeDescend, IntegralMaps.IntrinsicLinearMaps.rationalLift_id]
    exact LinearMap.ext (fun v => e.apply_symm_apply v)

instance nativeIntegralHodgeIso_isMonHom : IsMonHom (nativeIntegralHodgeIso e he hi hΛ).hom :=
  nativeHodgeDescend_isMonHom e.toLinearMap he (fun v hv => (hΛ v).mp hv)

theorem nativeIntegralHodgeIso_rational :
    IntegralMaps.IntrinsicLinearMaps.rationalLift (nativeIntegralHodgeIso e he hi hΛ).hom = e.toLinearMap :=
  rationalLift_nativeHodgeDescend e.toLinearMap he (fun v hv => (hΛ v).mp hv)

theorem nativeIntegralHodgeIso_inverse_rational :
    IntegralMaps.IntrinsicLinearMaps.rationalLift (nativeIntegralHodgeIso e he hi hΛ).inv = e.symm.toLinearMap :=
  rationalLift_nativeHodgeDescend e.symm.toLinearMap hi (nativeIntegralHodgeIso_inverse_lattice e hΛ)

theorem nativeIntegralHodgeIso_intertwines
    (a : A.toOver ⟶ A.toOver) (b : B.toOver ⟶ B.toOver) [IsMonHom a] [IsMonHom b]
    (hab : e.toLinearMap.comp (IntegralMaps.IntrinsicLinearMaps.rationalLift a) = (IntegralMaps.IntrinsicLinearMaps.rationalLift b).comp e.toLinearMap) :
    a ≫ (nativeIntegralHodgeIso e he hi hΛ).hom = (nativeIntegralHodgeIso e he hi hΛ).hom ≫ b := by
  apply IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful
  rw [IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, nativeIntegralHodgeIso_rational]
  exact hab

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeFullness.IntrinsicLinearMaps
