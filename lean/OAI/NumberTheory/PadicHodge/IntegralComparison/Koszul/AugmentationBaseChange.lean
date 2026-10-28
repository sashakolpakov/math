import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.PurityLocalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.BaseChange
import Mathlib.RingTheory.Regular.Flat

/-! # Augmentation Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.AugmentationBaseChange

noncomputable section

/-! The ordered Koszul scalar-extension map preserves the literal quotient
augmentation. This is the normalization needed for arbitrary resolutions. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.PurityLocalization

def quotientLinear {n : ℕ} (s : Fin n → R) :
    (R ⧸ OrientedTopCohomology.ideal R s) →ₗ[R] (S ⧸ OrientedTopCohomology.ideal S (algebraMap R S ∘ s)) where
  toAddHom := (PurityLocalization.quotientMap R S s).toAddMonoidHom
  map_smul' r x := by
    change PurityLocalization.quotientMap R S s (r • x) = r • PurityLocalization.quotientMap R S s x
    simp only [Algebra.smul_def, map_mul]
    congr 1

def tensorQuotient {n : ℕ} (s : Fin n → R) :
    S ⊗[R] (R ⧸ OrientedTopCohomology.ideal R s) →ₗ[S] (S ⧸ OrientedTopCohomology.ideal S (algebraMap R S ∘ s)) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : S →ₗ[S] S).smulRight (quotientLinear R S s))

omit [Module.Flat R S] in
theorem tensorQuotient_tmul {n : ℕ} (s : Fin n → R) (a : S) (x : R ⧸ OrientedTopCohomology.ideal R s) :
    tensorQuotient R S s (a ⊗ₜ[R] x) = a • PurityLocalization.quotientMap R S s x := rfl

theorem degree_zero {n : ℕ} (s : Fin n → R) (a : S) (x : ⋀[R]^0 (Fin n → R)) :
    exteriorPower.zeroEquiv S (Fin n → S)
        ((CoordinateBaseChange.iso R S s).hom.f 0 (a ⊗ₜ[R] x)) =
      a * algebraMap R S (exteriorPower.zeroEquiv R (Fin n → R) x) := by
  change exteriorPower.zeroEquiv S _ (exteriorPower.map 0
    (CoordinateBaseChange.coordinate R S n).toLinearMap
    (Exterior.ContractionBaseChange.power R S (Fin n → R) 0 (a ⊗ₜ[R] x))) = _
  have hz := LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality
    (CoordinateBaseChange.coordinate R S n).toLinearMap)
      (Exterior.ContractionBaseChange.power R S (Fin n → R) 0 (a ⊗ₜ[R] x))
  dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hz
  rw [hz]
  obtain ⟨r, rfl⟩ := (exteriorPower.zeroEquiv R (Fin n → R)).symm.surjective x
  rw [exteriorPower.zeroEquiv_symm_apply, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']
  rw [GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerEquiv_tmul_ιMulti, map_smul]
  simp [Algebra.smul_def, mul_comm]

theorem augmentation {n : ℕ} (s : Fin n → R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
    (hregS : RingTheory.Sequence.IsWeaklyRegular S (List.ofFn (algebraMap R S ∘ s))) :
    (CoordinateBaseChange.iso R S s).hom.f 0 ≫
        (Exterior.KoszulResolution.resolution S (algebraMap R S ∘ s) hregS).π.f 0 =
      (PurityLocalization.tensorFunctor R S).map ((Exterior.KoszulResolution.resolution R s hreg).π.f 0) ≫
        ModuleCat.ofHom (tensorQuotient R S s) := by
  rw [Exterior.KoszulResolution.resolution_π_f_zero,
    Exterior.KoszulResolution.resolution_π_f_zero]
  apply ModuleCat.hom_ext
  change (OrientedTopCohomology.ideal S (algebraMap R S ∘ s)).mkQ.comp
      ((exteriorPower.zeroEquiv S (Fin n → S)).toLinearMap.comp
        ((CoordinateBaseChange.iso R S s).hom.f 0).hom) =
    (tensorQuotient R S s).comp
      (((OrientedTopCohomology.ideal R s).mkQ.comp (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap).baseChange S)
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  change Ideal.Quotient.mk _ (exteriorPower.zeroEquiv S _
    ((CoordinateBaseChange.iso R S s).hom.f 0 (a ⊗ₜ[R] x))) =
      tensorQuotient R S s (a ⊗ₜ[R] Ideal.Quotient.mk _ (exteriorPower.zeroEquiv R _ x))
  rw [degree_zero, tensorQuotient_tmul]
  simp [PurityLocalization.quotientMap, map_mul, Algebra.smul_def]

theorem regular {n : ℕ} (s : Fin n → R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s)) :
    RingTheory.Sequence.IsWeaklyRegular S (List.ofFn (algebraMap R S ∘ s)) := by
  simpa using hreg.of_flat (S := S)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.AugmentationBaseChange
