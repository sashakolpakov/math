import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation

/-! # Smooth Witt Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrame

noncomputable section

/-! Smooth Witt lifts on affine charts define frames on the original global crystalline site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w))
  (X : Over (Spec (CommRingCat.of k)))
  (j : (Crystalline.Presentation.affineScheme k C).left ⟶ X.left)
  (hj : j ≫ X.hom = (Crystalline.Presentation.affineScheme k C).hom) (n : ℕ)

def frame : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) :=
  (BigCrystallineSite.postcompose j (Crystalline.OpenPresentation.overWitt p k C X j hj)).obj
    (SmoothWitt.WittFrame.object p k A C ρ hρ hker hbase n)

def boundedFrame : BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n :=
  ⟨frame p k A C ρ hρ hker hbase X j hj n, SmoothWitt.FrameRing.prime_power_zero p A n⟩

variable (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X))
  (t : Spec (CommRingCat.of (U.ring ⧸ U.ideal)) ⟶ (Crystalline.Presentation.affineScheme k C).left)
  (ht : t ≫ j = U.mapToX)

include ht in
theorem exists_map [Algebra.Smooth (WittVector p k) A] (hn : (p : U.ring) ^ (n + 1) = 0) :
    Nonempty (U ⟶ frame p k A C ρ hρ hker hbase X j hj n) := by
  let V := Crystalline.OpenPresentation.affineObject p k C X j hj U t ht
  obtain ⟨a⟩ := SmoothWitt.FrameCover.exists_morphism p k A C ρ hρ hker hbase n V hn
  refine ⟨{ ringMap := a.ringMap, overBase := a.overBase, overX := ?_ }⟩
  change BigCrystallineSite.Object.closed.map a ≫
    ((SmoothWitt.WittFrame.object p k A C ρ hρ hker hbase n).mapToX ≫ j) = U.mapToX
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ j) a.overX).trans ht)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrame
