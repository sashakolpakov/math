import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameTransition

/-! # Frame Transition Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameTransitionComposition

noncomputable section

/-! Canonical smooth Witt frame reductions satisfy identity and composition in the original crystalline category. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameTransition

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w))

theorem identity (n : ℕ) : FrameTransition.morphism p k A C ρ hρ hker hbase n n le_rfl = 𝟙 _ := by
  apply BigCrystallineSite.Object.Hom.ext
  apply DividedPowers.DPMorphism.ext
  exact congrArg DFunLike.coe (PD.TruncationTransition.map_refl A (Ideal.span {(p : A)}) n)

theorem composition (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) :
    FrameTransition.morphism p k A C ρ hρ hker hbase n m hnm ≫ FrameTransition.morphism p k A C ρ hρ hker hbase m l hml =
      FrameTransition.morphism p k A C ρ hρ hker hbase n l (hnm.trans hml) := by
  apply BigCrystallineSite.Object.Hom.ext
  apply DividedPowers.DPMorphism.ext
  exact congrArg DFunLike.coe (PD.TruncationTransition.map_comp A (Ideal.span {(p : A)}) n m hnm l hml)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameTransitionComposition
