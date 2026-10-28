import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.OpenFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.MonomorphismProducts

/-! # Etale Zero Frame Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.EtaleZeroFrameProduct

noncomputable section

/-!
# IntegralComparison: original étale zero-frame products over an arbitrary scheme
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [CharP k p]
  [CommRing C] [Algebra k C] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]
  (X : Over (Spec (CommRingCat.of k)))
  (j : (Crystalline.Presentation.affineScheme k C).left ⟶ X.left) [IsOpenImmersion j]
  (hj : j ≫ X.hom = (Crystalline.Presentation.affineScheme k C).hom)
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X))
  (α : U ⟶ ZeroLevel.OpenFrame.frame p k C X j hj)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.frame p k C
local notation "FG" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.OpenFrame.frame p k C X j hj
local notation "hjW" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation.overWitt p k C X j hj

abbrev localObject := Crystalline.Lifts.liftedObject j hjW (U := F) α
abbrev localMap := Crystalline.Lifts.liftedHom j hjW (U := F) α

local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.Open.EtaleZeroFrameProduct.localObject p k C X j hj U α
local notation "β" => OAI.NumberTheory.PadicHodge.IntegralComparison.Open.EtaleZeroFrameProduct.localMap p k C X j hj U α

def localCone : BinaryFan V F := EtaleZero.FrameMap.cone p k C σ V β

def mappedCone : BinaryFan ((BigCrystallineSite.postcompose j hjW).obj V) FG :=
  (localCone p k C σ X j hj U α).map (BigCrystallineSite.postcompose j hjW)

def cone : BinaryFan U FG := BinaryFan.mk
  ((mappedCone p k C σ X j hj U α).fst ≫ (Crystalline.Lifts.liftedIso j hjW (U := F) α).hom)
  (mappedCone p k C σ X j hj U α).snd

def isProduct : IsLimit (cone p k C σ X j hj U α) :=
  BinaryFan.isLimitCompLeftIso (mappedCone p k C σ X j hj U α)
    (Crystalline.Lifts.liftedIso j hjW (U := F) α).hom
    (Crystalline.MonomorphismProducts.productIsLimit j hjW
      (localCone p k C σ X j hj U α) (EtaleZero.FrameProduct.isProduct p k C σ V β))

abbrev productObject := (cone p k C σ X j hj U α).pt

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Open.EtaleZeroFrameProduct.productObject p k C σ X j hj U α

instance relativeAlgebra : Algebra U.ring (G).ring :=
  inferInstanceAs (Algebra U.ring (DividedPowerAlgebra U.ring (σ →₀ U.ring)))

def homotopyEquiv [Fintype σ] : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat U.ring)).obj (ModuleCat.of U.ring U.ring))
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex U.ring (G).ring (G).ideal (G).dividedPowers) :=
  Crystalline.DividedCoordinates.homotopyEquiv V σ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.EtaleZeroFrameProduct
