import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ReductionCharacterization
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrimePowerTransitionKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameTransition

/-! # Frame Reduction Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameReductionIso

noncomputable section

/-! The original smooth Witt frame transitions are canonically the prime-power reductions of the higher frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameTransition

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n m : ℕ) (hnm : n ≤ m)

theorem quotient_injective : Function.Injective (BigCrystallineSite.Object.quotientMap
    (WittFrame.object p k A C ρ hρ hker hbase n)
    (WittFrame.object p k A C ρ hρ hker hbase m)
    (FrameTransition.dpMap p k A n m hnm)) := by
  intro a b hab
  apply (FrameRing.quotientEquiv p A C ρ hρ hker m).injective
  exact (RingHom.congr_fun (FrameTransition.quotientMap_eq p k A C ρ hρ hker hbase n m hnm) a).symm.trans
    ((congrArg (FrameRing.quotientEquiv p A C ρ hρ hker n) hab).trans
      (RingHom.congr_fun (FrameTransition.quotientMap_eq p k A C ρ hρ hker hbase n m hnm) b))

def iso : WittFrame.object p k A C ρ hρ hker hbase n ≅
    Crystalline.LevelReduction.object n (WittFrame.object p k A C ρ hρ hker hbase m) :=
  Crystalline.ReductionCharacterization.iso n (FrameTransition.morphism p k A C ρ hρ hker hbase n m hnm)
    (FrameRing.prime_power_zero p A n)
    (PD.TruncationTransition.map_surjective A (Ideal.span {(p : A)}) n m hnm)
    (PrimePowerTransitionKernel.kernel p A n m hnm)
    (quotient_injective p k A C ρ hρ hker hbase n m hnm)

theorem iso_hom : (iso p k A C ρ hρ hker hbase n m hnm).hom ≫
    Crystalline.LevelReduction.hom n (WittFrame.object p k A C ρ hρ hker hbase m) =
      FrameTransition.morphism p k A C ρ hρ hker hbase n m hnm :=
  Crystalline.LevelReduction.factor_comp n (FrameTransition.morphism p k A C ρ hρ hker hbase n m hnm)
    (FrameRing.prime_power_zero p A n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameReductionIso
