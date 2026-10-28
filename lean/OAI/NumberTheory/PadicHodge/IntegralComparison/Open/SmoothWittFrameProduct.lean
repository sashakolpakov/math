import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.MonomorphismProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.DividedFlatness

/-! # Smooth Witt Frame Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrameProduct

noncomputable section

/-! Actual products with smooth Witt frames on monomorphic charts have free divided coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w))
  (X : Over (Spec (CommRingCat.of k)))
  (j : (Crystalline.Presentation.affineScheme k C).left ⟶ X.left) [Mono j]
  (hj : j ≫ X.hom = (Crystalline.Presentation.affineScheme k C).hom) (n : ℕ)
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X))
  (α : U ⟶ SmoothWittFrame.frame p k A C ρ hρ hker hbase X j hj n)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.object p k A C ρ hρ hker hbase n
local notation "FG" => OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrame.frame p k A C ρ hρ hker hbase X j hj n
local notation "hjW" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation.overWitt p k C X j hj

abbrev localObject := Crystalline.Lifts.liftedObject j hjW (U := F) α
abbrev localMap := Crystalline.Lifts.liftedHom j hjW (U := F) α

local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrameProduct.localObject p k A C ρ hρ hker hbase X j hj n U α
local notation "β" => OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrameProduct.localMap p k A C ρ hρ hker hbase X j hj n U α

def localCone : BinaryFan V F :=
  SmoothWitt.FrameDividedMap.cone p k A C ρ hρ hker hbase n V β σ

def mappedCone : BinaryFan ((BigCrystallineSite.postcompose j hjW).obj V) FG :=
  (localCone p k A C σ ρ hρ hker hbase X j hj n U α).map (BigCrystallineSite.postcompose j hjW)

def cone : BinaryFan U FG := BinaryFan.mk
  ((mappedCone p k A C σ ρ hρ hker hbase X j hj n U α).fst ≫
    (Crystalline.Lifts.liftedIso j hjW (U := F) α).hom)
  (mappedCone p k A C σ ρ hρ hker hbase X j hj n U α).snd

def isProduct : IsLimit (cone p k A C σ ρ hρ hker hbase X j hj n U α) :=
  BinaryFan.isLimitCompLeftIso (mappedCone p k A C σ ρ hρ hker hbase X j hj n U α)
    (Crystalline.Lifts.liftedIso j hjW (U := F) α).hom
    (Crystalline.MonomorphismProducts.productIsLimit j hjW
      (localCone p k A C σ ρ hρ hker hbase X j hj n U α)
      (SmoothWitt.FrameProduct.isProduct p k A C ρ hρ hker hbase n V β σ))

abbrev productObject := (cone p k A C σ ρ hρ hker hbase X j hj n U α).pt

omit [Mono j] in
theorem projection_flat : (cone p k A C σ ρ hρ hker hbase X j hj n U α).fst.ringMap.toRingHom.Flat :=
  Free.DividedFlatness.algebraMap_flat U.ring σ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrameProduct
