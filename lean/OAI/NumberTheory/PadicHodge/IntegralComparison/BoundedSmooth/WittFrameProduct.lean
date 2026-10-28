import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Witt Frame Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFrameProduct

noncomputable section

/-! Free divided coordinates for the native bounded smooth Witt frame product. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

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
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n

local instance structureMap_separated : IsSeparated f := by
  rw [Crystalline.Presentation.affine_wittStructureMap]
  exact inferInstanceAs (IsSeparated (Spec.map
    (CommRingCat.ofHom (Polynomial.Frobenius.coefficientReduction p k C))))

omit [CharP k p] [Module.Flat (WittVector p k) A] in
include σ in
theorem smooth : Algebra.Smooth W A := by
  let : Algebra.Smooth W (MvPolynomial σ W) := {}
  exact Algebra.Smooth.comp W (MvPolynomial σ W) A

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n)

def presentationMorphism : U ⟶ F := by
  letI := smooth p k A σ
  exact (SmoothWitt.FrameCover.bounded_cover p k A C ρ hρ hker hbase n U).some

def productIsLimit : IsLimit (BinaryFan.mk
    ((Q).map (prod.fst : F ⨯ U ⟶ F)) ((Q).map (prod.snd : F ⨯ U ⟶ U))) :=
  mapIsLimitOfPreservesOfIsLimit Q _ _ (prodIsProd F U)

def coordinateIso : Crystalline.DividedCoordinates.object U.obj σ ≅
    (BoundedFrame.Diagram.productDiagram F).obj U :=
  (BinaryFan.isLimitFlip (SmoothWitt.FrameProduct.isProduct p k A C ρ hρ hker hbase n U.obj
    ((Q).map (presentationMorphism p k A C σ ρ hρ hker hbase n U)) σ)).conePointUniqueUpToIso
      (productIsLimit p k A C ρ hρ hker hbase n U)

theorem coordinateIso_projection : (coordinateIso p k A C σ ρ hρ hker hbase n U).hom ≫
    (BoundedFrame.Diagram.projection F).app U = Crystalline.DividedCoordinates.projection U.obj σ := by
  rw [BoundedFrame.Diagram.projection_app]
  exact (BinaryFan.isLimitFlip (SmoothWitt.FrameProduct.isProduct p k A C ρ hρ hker hbase n U.obj
    ((Q).map (presentationMorphism p k A C σ ρ hρ hker hbase n U)) σ)).conePointUniqueUpToIso_hom_comp
      (productIsLimit p k A C ρ hρ hker hbase n U) ⟨WalkingPair.right⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFrameProduct
