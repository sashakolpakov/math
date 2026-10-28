import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizationFixedClass

/-! # Localized Fixed Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.LocalizedFixedClass

noncomputable section

/-! Clearing a boundary denominator and then its coefficient kernel
shows that localization kills only power-torsion in cohomology. In
particular, localization detects classes fixed by its parameter. -/
open _root_.CategoryTheory _root_.HomologicalComplex
universe u v
open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
variable {R : Type u} [CommRing R] (r : R)
  {K L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)
  (hsurj : ∀ q (y : L.X q), ∃ (a : ℕ) (x : K.X q), r^a • y = f.f q x)
  (hker : ∀ q (x : K.X q), f.f q x = 0 → ∃ a : ℕ, r^a • x = 0)

include hsurj hker in
theorem homology_kernel (n : ℕ) (x : K.homology n) (hx : homologyMap f n x = 0) :
    ∃ a : ℕ, r^a • x = 0 := by
  obtain ⟨u, rfl⟩ := Module.CochainClasses.classMap_surjective K n x
  have hu : Module.CochainClasses.classMap L n (Module.CochainClassNaturality.cycleMap f n u) = 0 :=
    (Module.CochainClassNaturality.naturality_apply f n u).trans hx
  obtain ⟨w, hw⟩ := (Module.CochainClasses.classMap_eq_zero_iff L n _).mp hu
  obtain ⟨a, v, hv⟩ := hsurj ((ComplexShape.up ℕ).prev n) w
  have hd : f.f n (K.d ((ComplexShape.up ℕ).prev n) n v) = r^a • (f.f n u.val) := by
    have hc := ConcreteCategory.congr_hom (f.comm ((ComplexShape.up ℕ).prev n) n) v
    change L.d ((ComplexShape.up ℕ).prev n) n (f.f _ v) =
      f.f n (K.d ((ComplexShape.up ℕ).prev n) n v) at hc
    rw [← hc, ← hv, map_smul, hw]
    rfl
  have he : f.f n (r^a • u.val - K.d ((ComplexShape.up ℕ).prev n) n v) = 0 := by
    rw [map_sub, map_smul, hd, sub_self]
  obtain ⟨b, hb⟩ := hker n _ he
  have hb' : r^b • (K.d ((ComplexShape.up ℕ).prev n) n v) = r^(b+a) • u.val := by
    rw [smul_sub, sub_eq_zero] at hb
    exact hb.symm.trans (by rw [pow_add, mul_smul])
  have hz : Module.CochainClasses.classMap K n (r^(b+a) • u) = 0 :=
    (Module.CochainClasses.classMap_eq_zero_iff K n _).mpr ⟨r^b • v,
      ((K.d ((ComplexShape.up ℕ).prev n) n).hom.map_smul _ _).trans hb'⟩
  exact ⟨b+a, by simpa only [map_smul] using hz⟩

include hsurj hker in
theorem eq_of_map_eq (n : ℕ) (x y : K.homology n)
    (hx : r • x = x) (hy : r • y = y) (h : homologyMap f n x = homologyMap f n y) : x = y := by
  have hz : homologyMap f n (x-y) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨a, ha⟩ := homology_kernel r f hsurj hker n (x-y) hz
  have hxy : r • (x-y) = x-y := by rw [smul_sub, hx, hy]
  rw [LocalizationFixedClass.pow_fixed r (x-y) hxy a] at ha
  exact sub_eq_zero.mp ha

variable (hloc : ∀ q, IsLocalizedModule.Away r (f.f q).hom)

include hloc in
theorem localized_eq (n : ℕ) (x y : K.homology n)
    (hx : r • x = x) (hy : r • y = y) (h : homologyMap f n x = homologyMap f n y) : x = y := by
  apply eq_of_map_eq r f (fun q y => ?_) (fun q x hx => ?_) n x y hx hy h
  · let := hloc q
    exact IsLocalizedModule.Away.surj (f.f q).hom r y
  · let := hloc q
    obtain ⟨a, ha⟩ := IsLocalizedModule.Away.exists_of_eq r
      (hx.trans ((f.f q).hom.map_zero).symm)
    exact ⟨a, by simpa only [smul_zero] using ha⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.LocalizedFixedClass
