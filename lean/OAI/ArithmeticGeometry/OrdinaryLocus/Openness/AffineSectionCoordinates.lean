import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PrincipalCech
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine Section Coordinates -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineSectionCoordinates.Construction

noncomputable section

/-! Localization coordinates for sections of quasicoherent sheaves on affine schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable (R : CommRingCat.{u}) (F : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of (PrimeSpectrum R)))
    (hF : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (F.obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom)

def affineBasicSectionEquiv (f : R) :
    Localization.Away f ⊗[R] F.obj.obj (op ⊤) ≃ₗ[R]
      F.obj.obj (op (PrimeSpectrum.basicOpen f)) := by
  let : IsLocalizedModule (Submonoid.powers f)
      (F.obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom := hF f
  exact IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (TensorProduct.mk R (Localization.Away f) (F.obj.obj (op ⊤)) 1)
    (F.obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom

theorem affineBasicSectionEquiv_unit (f : R) (m : F.obj.obj (op ⊤)) :
    affineBasicSectionEquiv R F hF f (1 ⊗ₜ[R] m) =
      F.obj.map (PrimeSpectrum.basicOpen f).leTop.op m := by
  let : IsLocalizedModule (Submonoid.powers f)
      (F.obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom := hF f
  change (IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (TensorProduct.mk R (Localization.Away f) (F.obj.obj (op ⊤)) 1)
    (F.obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom)
      ((TensorProduct.mk R (Localization.Away f) (F.obj.obj (op ⊤)) 1) m) =
        (F.obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom m
  apply IsLocalizedModule.linearEquiv_apply

theorem principalBasicOpen_le_of_dvd (f h : R) (hfh : f ∣ h) :
    PrimeSpectrum.basicOpen h ≤ PrimeSpectrum.basicOpen f := by
  intro p hp hpf
  exact hp (p.asIdeal.mem_of_dvd hfh hpf)

def affineBasicSectionRestriction (f h : R) (hfh : f ∣ h) :
    F.obj.obj (op (PrimeSpectrum.basicOpen f)) →ₗ[R]
      F.obj.obj (op (PrimeSpectrum.basicOpen h)) :=
  (F.obj.map (homOfLE (principalBasicOpen_le_of_dvd R f h hfh)).op).hom

theorem affineBasicSectionRestriction_comp (f g h : R) (hfg : f ∣ g) (hgh : g ∣ h) :
    affineBasicSectionRestriction R F g h hgh ∘ₗ affineBasicSectionRestriction R F f g hfg =
      affineBasicSectionRestriction R F f h (hfg.trans hgh) := by
  change (F.obj.map (homOfLE (principalBasicOpen_le_of_dvd R f g hfg)).op ≫
    F.obj.map (homOfLE (principalBasicOpen_le_of_dvd R g h hgh)).op).hom = _
  rw [← F.obj.map_comp]
  rfl

theorem affineBasicSectionRestriction_comp_apply (f g h : R) (hfg : f ∣ g) (hgh : g ∣ h)
    (x : F.obj.obj (op (PrimeSpectrum.basicOpen f))) :
    affineBasicSectionRestriction R F g h hgh (affineBasicSectionRestriction R F f g hfg x) =
      affineBasicSectionRestriction R F f h (hfg.trans hgh) x :=
  LinearMap.congr_fun (affineBasicSectionRestriction_comp R F f g h hfg hgh) x

theorem affineBasicSectionRestriction_naturality
    {G : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of (PrimeSpectrum R))} (φ : F ⟶ G)
    (f h : R) (hfh : f ∣ h) (x : F.obj.obj (op (PrimeSpectrum.basicOpen f))) :
    affineBasicSectionRestriction R G f h hfh (φ.hom.app _ x) =
      φ.hom.app _ (affineBasicSectionRestriction R F f h hfh x) :=
  (NatTrans.naturality_apply φ.hom
    (homOfLE (principalBasicOpen_le_of_dvd R f h hfh)).op x).symm

include hF in
theorem affineBasicSection_scalar_unit (f h : R) (hfh : f ∣ h) :
    ∀ x : Submonoid.powers f,
      IsUnit (algebraMap R (Module.End R (F.obj.obj (op (PrimeSpectrum.basicOpen h)))) x) := by
  let : IsLocalizedModule (Submonoid.powers h)
      (F.obj.map (PrimeSpectrum.basicOpen h).leTop.op).hom := hF h
  have hh : IsUnit
      ((algebraMap R (Module.End R (F.obj.obj (op (PrimeSpectrum.basicOpen h))))) h) :=
    IsLocalizedModule.map_units (S := Submonoid.powers h)
      (F.obj.map (PrimeSpectrum.basicOpen h).leTop.op).hom ⟨h, 1, by simp⟩
  obtain ⟨c, rfl⟩ := hfh
  have hf : IsUnit
      ((algebraMap R (Module.End R (F.obj.obj (op (PrimeSpectrum.basicOpen (f * c)))))) f) := by
    exact ((Commute.isUnit_mul_iff (.map (.all f c) _)).mp (by simpa using hh)).1
  rintro ⟨_, n, rfl⟩
  simpa using hf.pow n

theorem affineBasicSectionEquiv_restrict (f h : R) (hfh : f ∣ h) :
    affineBasicSectionRestriction R F f h hfh ∘ₗ (affineBasicSectionEquiv R F hF f).toLinearMap =
      (affineBasicSectionEquiv R F hF h).toLinearMap ∘ₗ
        PrincipalOverlaps.Construction.principalRestrictionModule R (F.obj.obj (op ⊤)) f h hfh := by
  apply IsLocalizedModule.ext (Submonoid.powers f)
    (TensorProduct.mk R (Localization.Away f) (F.obj.obj (op ⊤)) 1)
    (affineBasicSection_scalar_unit R F hF f h hfh)
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.mk_apply,
    affineBasicSectionEquiv_unit R F hF]
  change F.obj.map (homOfLE (principalBasicOpen_le_of_dvd R f h hfh)).op
      (F.obj.map (PrimeSpectrum.basicOpen f).leTop.op m) = _
  rw [← ModuleCat.comp_apply, ← F.obj.map_comp]
  change F.obj.map (PrimeSpectrum.basicOpen h).leTop.op m = _
  simp [PrincipalOverlaps.Construction.principalRestrictionModule, affineBasicSectionEquiv_unit R F hF]

theorem affineBasicSectionEquiv_restrict_apply (f h : R) (hfh : f ∣ h)
    (z : Localization.Away f ⊗[R] F.obj.obj (op ⊤)) :
    affineBasicSectionRestriction R F f h hfh (affineBasicSectionEquiv R F hF f z) =
      affineBasicSectionEquiv R F hF h
        (PrincipalOverlaps.Construction.principalRestrictionModule R (F.obj.obj (op ⊤)) f h hfh z) :=
  LinearMap.congr_fun (affineBasicSectionEquiv_restrict R F hF f h hfh) z

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineSectionCoordinates.Construction
