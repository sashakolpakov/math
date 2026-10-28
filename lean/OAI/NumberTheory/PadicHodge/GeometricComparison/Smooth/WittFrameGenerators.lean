import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Witt Frame Generators -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameGenerators.SmoothWittFrameGenerators

noncomputable section

/-! Generators for finite smooth Witt frames and their geometric postcomposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v
variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

def generators : A → (IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n).obj.ring :=
  Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1))

theorem surjective : Function.Surjective (generators p k A C ρ hρ hker hbase n) :=
  Ideal.Quotient.mk_surjective

variable {r : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (m : ℕ)
  (F : IntegralComparison.BoundedCrystalline.Site.Objects (p := r) (J := J) (δ := δ) f m)
  {D : Type v} (q : D → F.obj.ring)

def postcompose : D → ((IntegralComparison.BoundedOpen.Equivalence.postcompose g hg m).obj F).obj.ring := q

theorem postcompose_surjective (hq : Function.Surjective q) :
    Function.Surjective (postcompose g hg m F q) := hq

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameGenerators.SmoothWittFrameGenerators
