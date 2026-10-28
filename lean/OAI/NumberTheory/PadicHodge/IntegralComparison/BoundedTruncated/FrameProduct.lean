import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Frame Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct

noncomputable section

/-! Free divided coordinates for the native bounded smooth finite-level frame product. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C σ : Type) [CommRing A] [CommRing C]
  [Algebra (Truncated.Witt.Ring p k n) A]
  [Algebra.Smooth (Truncated.Witt.Ring p k n) A] [Algebra k C]
  [Fintype σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [IsScalarTower (Truncated.Witt.Ring p k n)
    (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Truncated.Witt.Ring p k n) A (Truncated.Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.boundedFrame p A C ρ hρ hker k n hbase
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n

local instance structureMap_separated : IsSeparated f := by
  rw [Crystalline.Presentation.affine_wittStructureMap]
  exact inferInstanceAs (IsSeparated (Spec.map
    (CommRingCat.ofHom (Polynomial.Frobenius.coefficientReduction p k C))))

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n)

def presentationMorphism : U ⟶ F := by
  exact (Truncated.FrameAlgebras.SmoothLifting.exists_morphism p k n A C ρ hbase U hρ hker).some

def productIsLimit : IsLimit (BinaryFan.mk
    ((Q).map (prod.fst : F ⨯ U ⟶ F)) ((Q).map (prod.snd : F ⨯ U ⟶ U))) :=
  mapIsLimitOfPreservesOfIsLimit Q _ _ (prodIsProd F U)

def coordinateIso : Crystalline.DividedCoordinates.object U.obj σ ≅
    (BoundedFrame.Diagram.productDiagram F).obj U :=
  (BinaryFan.isLimitFlip (Truncated.FrameProduct.isProduct p k n A C ρ hρ hker hbase U.obj
    ((Q).map (presentationMorphism p k n A C ρ hρ hker hbase U)) σ)).conePointUniqueUpToIso
      (productIsLimit p k n A C ρ hρ hker hbase U)

omit [Fintype k] [Fintype σ] in
theorem coordinateIso_projection : (coordinateIso p k n A C σ ρ hρ hker hbase U).hom ≫
    (BoundedFrame.Diagram.projection F).app U = Crystalline.DividedCoordinates.projection U.obj σ := by
  rw [BoundedFrame.Diagram.projection_app]
  exact (BinaryFan.isLimitFlip (Truncated.FrameProduct.isProduct p k n A C ρ hρ hker hbase U.obj
    ((Q).map (presentationMorphism p k n A C ρ hρ hker hbase U)) σ)).conePointUniqueUpToIso_hom_comp
      (productIsLimit p k n A C ρ hρ hker hbase U) ⟨WalkingPair.right⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct
