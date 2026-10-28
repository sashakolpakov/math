import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RowRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSectionMap

/-! # Diagonal Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalCech.IntrinsicPadicGeometricDiagonalCech

noncomputable section

/-! The native diagonal-to-Cech section comparison commutes with
geometric pullback over each finite compatible affine-pair family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [Smooth X₁.hom] [Smooth X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  {ι : Type} [Finite ι] (U : ι → Affine.MapPairs.AffineMapPairs.Charts u.left)

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
local notation "W" => WittVector p (ZMod p)
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "Pairs" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.Charts (Over.Hom.left u)
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Over.Hom.left v) (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "P" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₂ Y₂ f₂ hp₂ n
local notation "Q" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₁ Y₁ f₁ hp₁ n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ResolutionDiagram.IntrinsicPadicGeometricResolutionDiagram.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.targetSections p u f₂ n
local notation "S'" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.sourceSections p u f₁ n
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.transformation p u v f₁ f₂ hsquare n

local instance sourceCoproducts : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w₁ n) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (IntegralComparison.BoundedCrystalline.Site.topology w₁ n)
local instance targetCoproducts : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w₂ n) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (IntegralComparison.BoundedCrystalline.Site.topology w₂ n)

def diagonalMap : Section.DiagonalCone.SectionDiagonalCone.source Pairs S P ⟶ Section.DiagonalCone.SectionDiagonalCone.source Pairs S' Q :=
  Section.DiagonalConeChange.SectionDiagonalConeChange.diagonalMap Pairs T S S' P Q a b

def totalSectionsMap : ((S).mapHomologicalComplex (.up ℕ)).obj (CechCone.Total.CechConeTotal.total U P) ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj (CechCone.Total.CechConeTotal.total U Q) :=
  CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.map T S S' U P Q a b

def targetComparison : Section.DiagonalCone.SectionDiagonalCone.source Pairs S P ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj (CechCone.Total.CechConeTotal.total U P) :=
  Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} Pairs R S P
    (RowRestriction.IntrinsicPadicGeometricRowRestriction.target_meet_isIso p u f₂ hp₂ n) U

def sourceComparison : Section.DiagonalCone.SectionDiagonalCone.source Pairs S' Q ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj (CechCone.Total.CechConeTotal.total U Q) :=
  Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} Pairs R S' Q
    (RowRestriction.IntrinsicPadicGeometricRowRestriction.source_meet_isIso p u f₁ hp₁ n) U

theorem natural : targetComparison p u f₂ hp₂ n U ≫ totalSectionsMap p u v f₁ f₂ hp₁ hp₂ hsquare n U =
    diagonalMap p u v f₁ f₂ hp₁ hp₂ hsquare n ≫ sourceComparison p u f₁ hp₁ n U :=
  Section.DiagonalCechChange.SectionDiagonalCechChange.natural.{0, 2, 1, 2, 1, 1, 2} Pairs R T S S' P Q a b
    (RowRestriction.IntrinsicPadicGeometricRowRestriction.target_meet_isIso p u f₂ hp₂ n)
    (RowRestriction.IntrinsicPadicGeometricRowRestriction.source_meet_isIso p u f₁ hp₁ n) U

theorem totalSectionsMap_eq : totalSectionsMap p u v f₁ f₂ hp₁ hp₂ hsquare n U =
    Section.CochainPullback.SectionCochainPullback.map T S S' b (CechDiagram.IntrinsicPadicGeometricCechDiagram.map p u v f₁ f₂ hp₁ hp₂ hsquare n U) :=
  CechCone.TotalSectionMap.CechConeTotalSectionMap.map_eq T S S' U P Q a b

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalCech.IntrinsicPadicGeometricDiagonalCech
