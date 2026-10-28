import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NilpotentCechConstants
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainZero
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleTensor
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalComplexRigidity
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Cech Constants -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.CechConstants.Construction

noncomputable section

/-! A finite free model detects all degree-zero cycles from its
residue complex. The model need not contain a chosen lift of constants. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits TensorProduct

universe u
variable {R : Type u} [CommRing R]
  {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : D ⟶ C)

set_option backward.isDefEq.respectTransparency false in
theorem cochain_zero_cycle_eq_zero [QuasiIsoAt φ 0]
    (x : D.X 0) (hx : D.d 0 1 x = 0) (hφx : φ.f 0 x = 0) : x = 0 := by
  let z : (D.d 0 1).hom.ker := ⟨x, hx⟩
  have hz : Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv φ z = 0 := by
    apply Subtype.ext
    rw [Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val]
    exact hφx
  have := (Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv φ).injective (hz.trans (map_zero _).symm)
  exact congrArg Subtype.val this

set_option backward.isDefEq.respectTransparency false in
theorem finite_model_residue_detector_injective
    (k : Type u) [AddCommGroup k] [Module R k] [QuasiIsoAt (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map k φ) 0]
    (a : R →ₗ[R] C.X 0) (e : C.X 0 →ₗ[R] R)
    (hea : e.comp a = LinearMap.id)
    (hres : Function.Exact (a.lTensor k) ((C.d 0 1).hom.lTensor k)) :
    Function.Injective (((e.comp (φ.f 0).hom).prod (D.d 0 1).hom).lTensor k) := by
  let b := (e.comp (φ.f 0).hom).prod (D.d 0 1).hom
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  change b.lTensor k x = 0 at hx
  have he : (e.comp (φ.f 0).hom).lTensor k x = 0 := by
    have h := congrArg ((LinearMap.fst R R (D.X 1)).lTensor k) hx
    have hp : (LinearMap.fst R R (D.X 1)).comp b = e.comp (φ.f 0).hom := by ext z; rfl
    simpa only [← LinearMap.lTensor_comp_apply, hp, map_zero] using h
  have hd : (D.d 0 1).hom.lTensor k x = 0 := by
    have h := congrArg ((LinearMap.snd R R (D.X 1)).lTensor k) hx
    have hp : (LinearMap.snd R R (D.X 1)).comp b = (D.d 0 1).hom := by ext z; rfl
    simpa only [← LinearMap.lTensor_comp_apply, hp, map_zero] using h
  let y := (φ.f 0).hom.lTensor k x
  have hy : (C.d 0 1).hom.lTensor k y = 0 := by
    have hc : (C.d 0 1).hom.comp (φ.f 0).hom = (φ.f 1).hom.comp (D.d 0 1).hom :=
      congrArg ModuleCat.Hom.hom (φ.comm 0 1)
    change (C.d 0 1).hom.lTensor k ((φ.f 0).hom.lTensor k x) = 0
    rw [← LinearMap.lTensor_comp_apply, hc, LinearMap.lTensor_comp_apply, hd, map_zero]
  obtain ⟨r, hr⟩ := (hres y).mp hy
  have hr0 : r = 0 := by
    have h : e.lTensor k y = 0 := by
      simpa only [y, ← LinearMap.lTensor_comp_apply] using he
    rw [← hr, ← LinearMap.lTensor_comp_apply, hea, LinearMap.lTensor_id, LinearMap.id_apply] at h
    exact h
  have hy0 : y = 0 := by rw [← hr, hr0, map_zero]
  exact cochain_zero_cycle_eq_zero (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map k φ) x hd hy0

set_option backward.isDefEq.respectTransparency false in
theorem finite_model_cycle_constants [IsLocalRing R] [QuasiIsoAt φ 0]
    [Module.Finite R (D.X 0)] [Module.Finite R (D.X 1)] [Module.Free R (D.X 1)]
    [QuasiIsoAt (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map (IsLocalRing.ResidueField R) φ) 0]
    (a : R →ₗ[R] C.X 0) (e : C.X 0 →ₗ[R] R)
    (hea : e.comp a = LinearMap.id) (hda : (C.d 0 1).hom.comp a = 0)
    (hres : Function.Exact (a.lTensor (IsLocalRing.ResidueField R))
      ((C.d 0 1).hom.lTensor (IsLocalRing.ResidueField R)))
    (x : C.X 0) (hx : C.d 0 1 x = 0) : x = a (e x) := by
  let b := (e.comp (φ.f 0).hom).prod (D.d 0 1).hom
  have : Module.Flat R (R × D.X 1) := Quotients.FiniteDescent.FlatKernelProd.Construction.FlatKernel.prod
  have : Module.Free R (R × D.X 1) := Module.free_of_flat_of_isLocalRing
  have hb : Function.Injective b := Quotients.FiniteDescent.LocalComplexRigidity.Construction.LocalSectionLifting.linearMap_injective_of_residue_injective b
    (finite_model_residue_detector_injective φ (IsLocalRing.ResidueField R) a e hea hres)
  let z : (C.d 0 1).hom.ker := ⟨x - a (e x), by
    change (C.d 0 1).hom (x - a (e x)) = 0
    rw [map_sub, hx, ← LinearMap.comp_apply, hda, LinearMap.zero_apply, sub_self]⟩
  let w := (Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv φ).symm z
  have hw : φ.f 0 w.val = z.val := by
    rw [← Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val, LinearEquiv.apply_symm_apply]
  have hw0 : b w.val = 0 := by
    apply Prod.ext
    · change e (φ.f 0 w.val) = 0
      rw [hw]
      change e (x - a (e x)) = 0
      rw [map_sub, ← LinearMap.comp_apply, hea, LinearMap.id_apply, sub_self]
    · exact w.property
  have hzero : w.val = 0 := hb (hw0.trans (map_zero b).symm)
  have hz : z.val = 0 := by rw [← hw, hzero, map_zero]
  exact sub_eq_zero.mp hz

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.CechConstants.Construction
