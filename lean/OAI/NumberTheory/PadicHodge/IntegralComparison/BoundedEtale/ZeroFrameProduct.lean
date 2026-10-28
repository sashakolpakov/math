import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Zero Frame Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFrameProduct

noncomputable section

/-!
# IntegralComparison: divided coordinates for the native zeroth-level étale frame product
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [Fintype σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0

instance structureMap_separated : IsSeparated f := by
  rw [Crystalline.Presentation.affine_wittStructureMap]
  exact inferInstanceAs (IsSeparated (Spec.map
    (CommRingCat.ofHom (Polynomial.Frobenius.coefficientReduction p k C))))

omit [Fact p.Prime] [Fintype k] [CharP k p] in
include σ in
theorem smooth : Algebra.Smooth k C := by
  let : Algebra.Smooth k (MvPolynomial σ k) := {}
  exact Algebra.Smooth.comp k (MvPolynomial σ k) C

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0)

def presentationMorphism : U ⟶ F := by
  letI := smooth k C σ
  have hz : (p : U.obj.ring) = 0 := (pow_one (p : U.obj.ring)).symm.trans U.property
  exact ObjectProperty.homMk (ZeroLevel.LevelFrame.exists_map p k C U.obj hz).some

def productIsLimit : IsLimit (BinaryFan.mk
    ((Q).map (prod.fst : F ⨯ U ⟶ F)) ((Q).map (prod.snd : F ⨯ U ⟶ U))) :=
  mapIsLimitOfPreservesOfIsLimit Q _ _ (prodIsProd F U)

def coordinateIso : Crystalline.DividedCoordinates.object U.obj σ ≅
    (BoundedFrame.Diagram.productDiagram F).obj U :=
  (BinaryFan.isLimitFlip (EtaleZero.FrameProduct.isProduct p k C σ U.obj
    ((Q).map (presentationMorphism p k C σ U)))).conePointUniqueUpToIso
      (productIsLimit p k C U)

theorem coordinateIso_projection : (coordinateIso p k C σ U).hom ≫
    (BoundedFrame.Diagram.projection F).app U = Crystalline.DividedCoordinates.projection U.obj σ := by
  rw [BoundedFrame.Diagram.projection_app]
  exact (BinaryFan.isLimitFlip (EtaleZero.FrameProduct.isProduct p k C σ U.obj
    ((Q).map (presentationMorphism p k C σ U)))).conePointUniqueUpToIso_hom_comp
      (productIsLimit p k C U) ⟨WalkingPair.right⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFrameProduct
