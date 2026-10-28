import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameTransition
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionChange

/-! # Level Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.LevelMap

noncomputable section

/-! Canonical p-power quotient maps induce augmented maps on the original smooth Witt frame resolutions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "Fn" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n
local notation "Fm" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase m
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n m hnm
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n m hnm

local instance structureMap_separated : IsSeparated f := by
  rw [Crystalline.Presentation.affine_wittStructureMap]
  exact inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom
    (Polynomial.Frobenius.coefficientReduction p k C))))

def morphism : (G).obj Fn ⟶ Fm :=
  ObjectProperty.homMk (FrameTransition.morphism p k A C ρ hρ hker hbase n m hnm)

def sheafMap : ((T).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (Bounded.RelativeSheafComplex.complex f m Fm) ⟶ Bounded.RelativeSheafComplex.complex f n Fn :=
  BoundedLevel.FrameMap.map f n m hnm (morphism p k A C ρ hρ hker hbase n m hnm)

theorem augmentation : BoundedLevel.PulledAugmentation.augmentation f n m hnm Fm ≫
    sheafMap p k A C ρ hρ hker hbase n m hnm = Bounded.RelativeSheafComplex.augmentation f n Fn :=
  BoundedLevel.FrameMap.augmentation f n m hnm (morphism p k A C ρ hρ hker hbase n m hnm)

def rawFrameMap : RelativeFrame.ComplexMap.frameComplex (Fm).obj ⟶
    RelativeFrame.ComplexMap.frameComplex (Fn).obj :=
  RelativeFrame.ChangeNaturality.frameMap (Fm).obj (Fn).obj
    (FrameTransition.morphism p k A C ρ hρ hker hbase n m hnm)

def frameMap : BoundedFrame.DeRhamSections.frameComplex f m Fm ⟶
    BoundedFrame.DeRhamSections.frameComplex f n Fn :=
  ((Crystalline.RelativeResolution.coefficientFunctor (B := W)).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (rawFrameMap p k A C ρ hρ hker hbase n m hnm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.LevelMap
