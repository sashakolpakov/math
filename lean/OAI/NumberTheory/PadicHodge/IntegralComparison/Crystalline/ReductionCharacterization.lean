import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReductionFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Isomorphism
import OAI.NumberTheory.PadicHodge.IntegralComparison.RingQuotientFactor

/-! # Reduction Characterization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ReductionCharacterization

noncomputable section

/-! The canonical level reduction agrees with any original crystalline quotient having the same prime-power kernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReduction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {δ : DividedPowers (Ideal.span {(p : B)})}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (n : ℕ)
  {U V : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f} (α : U ⟶ V)
  (hU : (p : U.ring) ^ (n + 1) = 0)
  (hα : Function.Surjective α.ringMap)
  (hk : RingHom.ker α.ringMap.toRingHom = (Ideal.span {(p : V.ring)}) ^ (n + 1))
  (hq : Function.Injective (BigCrystallineSite.Object.quotientMap U V α.ringMap))

include hα hk in
theorem factor_bijective : Function.Bijective (LevelReduction.factor n α hU).ringMap :=
  RingQuotientFactor.bijective (LevelReduction.hom n V).ringMap.toRingHom α.ringMap.toRingHom
    (LevelReduction.factor n α hU).ringMap.toRingHom (LevelReduction.hom_surjective n V) hα
    (congrArg (fun a : U ⟶ V => a.ringMap.toRingHom) (LevelReduction.factor_comp n α hU))
    ((LevelReduction.hom_kernel n V).trans hk.symm)

include hq in
theorem factor_quotient_injective : Function.Injective (BigCrystallineSite.Object.quotientMap U (LevelReduction.object n V) (LevelReduction.factor n α hU).ringMap) := by
  have hs : Function.Surjective (BigCrystallineSite.Object.quotientMap (LevelReduction.object n V) V (LevelReduction.hom n V).ringMap) :=
    Ideal.quotientMap_surjective (LevelReduction.hom_surjective n V)
  have he : (BigCrystallineSite.Object.quotientMap U (LevelReduction.object n V) (LevelReduction.factor n α hU).ringMap).comp
      (BigCrystallineSite.Object.quotientMap (LevelReduction.object n V) V (LevelReduction.hom n V).ringMap) = BigCrystallineSite.Object.quotientMap U V α.ringMap := by
    rw [← BigCrystallineSite.Object.quotientMap_comp]
    exact congrArg (fun a : U ⟶ V => BigCrystallineSite.Object.quotientMap U V a.ringMap) (LevelReduction.factor_comp n α hU)
  intro x y hxy
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  have hab : BigCrystallineSite.Object.quotientMap U V α.ringMap a = BigCrystallineSite.Object.quotientMap U V α.ringMap b :=
    (RingHom.congr_fun he a).symm.trans (hxy.trans (RingHom.congr_fun he b))
  exact congrArg (BigCrystallineSite.Object.quotientMap (LevelReduction.object n V) V (LevelReduction.hom n V).ringMap) (hq hab)

include hα hk hq in
theorem factor_isIso : IsIso (LevelReduction.factor n α hU) :=
  Isomorphism.isIso_of_ring_bijective_quotient_injective (LevelReduction.factor n α hU)
    (factor_bijective n α hU hα hk) (factor_quotient_injective n α hU hq)

def iso : U ≅ LevelReduction.object n V :=
  Isomorphism.iso (LevelReduction.factor n α hU)
    (factor_bijective n α hU hα hk) (factor_quotient_injective n α hU hq)

theorem iso_hom : (iso n α hU hα hk hq).hom ≫ LevelReduction.hom n V = α := LevelReduction.factor_comp n α hU

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ReductionCharacterization
