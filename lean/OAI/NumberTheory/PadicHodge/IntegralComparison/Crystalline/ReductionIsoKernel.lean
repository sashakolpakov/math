import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeIso

/-! # Reduction Iso Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ReductionIsoKernel

noncomputable section

/-! An actual crystalline reduction retains its exact quotient kernel after a source isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReduction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {δ : DividedPowers (Ideal.span {(p : B)})}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (n : ℕ)
  {U V : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f} (e : U ≅ LevelReduction.object n V)

def morphism : U ⟶ V := e.hom ≫ LevelReduction.hom n V

theorem surjective : Function.Surjective (morphism n e).ringMap :=
  (RelativeIso.ringEquiv e).surjective.comp (LevelReduction.hom_surjective n V)

theorem kernel : RingHom.ker (morphism n e).ringMap.toRingHom = (Ideal.span {(p : V.ring)}) ^ (n + 1) :=
  (RingHom.ker_comp_of_injective (LevelReduction.hom n V).ringMap.toRingHom
    (RelativeIso.ringEquiv e).injective).trans (LevelReduction.hom_kernel n V)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ReductionIsoKernel
