import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.FrameSliceQuasiIso

/-! # Witt Global Slice Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittGlobalSliceResolution.SmoothWittGlobalSliceResolution

noncomputable section

/-! The actual smooth Witt frame Poincare comparison holds on the original
slice of its globally postcomposed frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C] [Fintype σ]
  [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n

local instance structureMap_separated : IsSeparated f :=
  IntegralComparison.BoundedSmooth.WittFrameProduct.structureMap_separated p k C

variable {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of (WittVector p k))}
  [IsSeparated fY] (g : (IntegralComparison.Crystalline.Presentation.affineScheme k C).left ⟶ Y) [Mono g]
  (hg : g ≫ fY = IntegralComparison.Witt.Crystalline.wittStructureMap p k (IntegralComparison.Crystalline.Presentation.affineScheme k C))

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) g hg n

include σ in
theorem onSlice : QuasiIso
    (((PresheafRestriction.PresheafRestrictionQuasiIso.restriction (V := ModuleCat.{u} W)
      (Over.forget ((G).obj F))).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.BoundedFrame.Diagram.augmentation ((G).obj F))) := by
  let : QuasiIso (IntegralComparison.BoundedFrame.Diagram.augmentation F) :=
    IntegralComparison.BoundedSmooth.WittResolution.presheaf_augmentation_quasiIso p k A C σ ρ hρ hker hbase n
  exact FrameSliceQuasiIso.OpenFrameSliceQuasiIso.onSlice g hg n F

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittGlobalSliceResolution.SmoothWittGlobalSliceResolution
