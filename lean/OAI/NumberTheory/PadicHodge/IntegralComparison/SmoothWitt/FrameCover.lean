import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameMap

/-! # Frame Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameCover

noncomputable section

/-! Smooth Witt frames receive every object at their prescribed original crystalline level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Algebra.Smooth (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

omit [Fintype k] in
theorem exists_morphism
    (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
      (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
    (hn : (p : U.ring) ^ (n + 1) = 0) :
    Nonempty (U ⟶ WittFrame.object p k A C ρ hρ hker hbase n) := by
  obtain ⟨l, hl, hb⟩ := FrameLifting.exists_lift p k A C ρ hbase U
  exact ⟨FrameMap.morphism p k A C ρ hρ hker hbase n U hn l hl hb⟩

omit [Fintype k] in
theorem bounded_cover
    (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n) :
    Nonempty (U ⟶ WittFrame.boundedFrame p k A C ρ hρ hker hbase n) := by
  obtain ⟨f⟩ := exists_morphism p k A C ρ hρ hker hbase n U.obj U.property
  exact ⟨ObjectProperty.homMk f⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameCover
