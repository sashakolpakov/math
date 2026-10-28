import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameReductionIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReductionAdjunction

/-! # Smooth Witt Frame Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrameReduction

noncomputable section

/-! Original Witt frame transitions on global charts are their canonical level reductions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w))
  (X : Over (Spec (CommRingCat.of k))) (j : (Crystalline.Presentation.affineScheme k C).left ⟶ X.left)
  (hj : j ≫ X.hom = (Crystalline.Presentation.affineScheme k C).hom) (n m : ℕ) (hnm : n ≤ m)

def morphism : SmoothWittFrame.frame p k A C ρ hρ hker hbase X j hj n ⟶
    SmoothWittFrame.frame p k A C ρ hρ hker hbase X j hj m :=
  (BigCrystallineSite.postcompose j (Crystalline.OpenPresentation.overWitt p k C X j hj)).map
    (SmoothWitt.FrameTransition.morphism p k A C ρ hρ hker hbase n m hnm)

def iso : SmoothWittFrame.frame p k A C ρ hρ hker hbase X j hj n ≅
    Crystalline.LevelReduction.object n (SmoothWittFrame.frame p k A C ρ hρ hker hbase X j hj m) :=
  Crystalline.ReductionCharacterization.iso n (morphism p k A C ρ hρ hker hbase X j hj n m hnm)
    (SmoothWitt.FrameRing.prime_power_zero p A n)
    (PD.TruncationTransition.map_surjective A (Ideal.span {(p : A)}) n m hnm)
    (PrimePowerTransitionKernel.kernel p A n m hnm)
    (SmoothWitt.FrameReductionIso.quotient_injective p k A C ρ hρ hker hbase n m hnm)

theorem iso_hom : (iso p k A C ρ hρ hker hbase X j hj n m hnm).hom ≫
    Crystalline.LevelReduction.hom n (SmoothWittFrame.frame p k A C ρ hρ hker hbase X j hj m) =
      morphism p k A C ρ hρ hker hbase X j hj n m hnm :=
  Crystalline.LevelReduction.factor_comp n (morphism p k A C ρ hρ hker hbase X j hj n m hnm)
    (SmoothWitt.FrameRing.prime_power_zero p A n)

def boundedIso : SmoothWittFrame.boundedFrame p k A C ρ hρ hker hbase X j hj n ≅
    (Crystalline.LevelReductionFunctor.functor n).obj
      (SmoothWittFrame.frame p k A C ρ hρ hker hbase X j hj m) :=
  (BoundedCrystalline.Site.property (Witt.Crystalline.wittStructureMap p k X) n).isoMk
    (iso p k A C ρ hρ hker hbase X j hj n m hnm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrameReduction
