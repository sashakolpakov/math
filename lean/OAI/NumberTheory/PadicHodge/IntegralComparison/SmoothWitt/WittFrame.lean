import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

/-! # Witt Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame

noncomputable section

/-! The smooth Witt lift defines actual frames in every original bounded crystalline site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

local notation "W" => WittVector p k
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.quotientEquiv p A C ρ hρ hker n

def object : BigCrystallineSite.Object p W (Ideal.span {(p : W)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) where
  ring := CommRingCat.of (FrameRing.Ring p A n)
  base := FrameRing.base p k A n
  ideal := FrameRing.ideal p A n
  dividedPowers := FrameRing.dividedPowers p k A n
  baseCompatible := FrameRing.base_isDPMorphism p k A n
  primeNilpotent := ⟨n + 1, FrameRing.prime_power_zero p A n⟩
  nilIdeal := fun _ ha => DividedPower.Nilpotence.nilpotent_of_mem (FrameRing.dividedPowers p k A n)
    p (Fact.out : p.Prime).pos ⟨n + 1, FrameRing.prime_power_zero p A n⟩ ha
  mapToX := Spec.map (CommRingCat.ofHom (e).symm.toRingHom)
  overBase := by
    rw [Crystalline.Presentation.affine_wittStructureMap]
    change Spec.map (CommRingCat.ofHom (e).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap k C).comp WittVector.constantCoeff)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (FrameRing.ideal p A n))) ≫
        Spec.map (CommRingCat.ofHom (FrameRing.base p k A n))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    apply (e).injective
    change (e) ((e).symm (algebraMap k C (WittVector.constantCoeff w))) =
      (e) (Ideal.Quotient.mk (FrameRing.ideal p A n) (FrameRing.base p k A n w))
    rw [RingEquiv.apply_symm_apply, FrameRing.quotientEquiv_base p k A C ρ hρ hker hbase]

def boundedFrame : BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n :=
  ⟨object p k A C ρ hρ hker hbase n, FrameRing.prime_power_zero p A n⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame
