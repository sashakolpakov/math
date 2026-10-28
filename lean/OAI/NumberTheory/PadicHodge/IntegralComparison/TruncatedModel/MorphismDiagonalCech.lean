import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRowRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSectionMap

/-! # Morphism Diagonal Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalCech

noncomputable section

/-! The native diagonal-to-Cech section comparison commutes with
geometric pullback over each finite compatible affine-pair family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [Smooth X₁.hom] [Smooth X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  {ι : Type} [Finite ι] (U : ι → AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)

open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames
local notation "W" => WittVector p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "Pairs" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts (Over.Hom.left u)
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Over.Hom.left v) (MorphismData.Frames.ambient_over p k v) n
local notation "P" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₂ Y₂ f₂ hp₂
local notation "Q" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₁ Y₁ f₁ hp₁
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismResolution.transformation p k n u v f₁ f₂ hp₁ hp₂ sq
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.targetSections p k n u f₂
local notation "S'" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.sourceSections p k n u f₁
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.transformation p k n u v f₁ f₂ sq

local instance sourceCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₁ n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (BoundedCrystalline.Site.topology w₁ n)
local instance targetCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₂ n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (BoundedCrystalline.Site.topology w₂ n)

def diagonalMap : GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source Pairs S P ⟶ GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source Pairs S' Q :=
  GeometricComparison.Section.DiagonalConeChange.SectionDiagonalConeChange.diagonalMap Pairs T S S' P Q a b

def totalSectionsMap : ((S).mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.CechCone.Total.CechConeTotal.total U P) ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.CechCone.Total.CechConeTotal.total U Q) :=
  GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.map T S S' U P Q a b

def targetComparison : GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source Pairs S P ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.CechCone.Total.CechConeTotal.total U P) :=
  GeometricComparison.Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} Pairs R S P
    (MorphismRowRestriction.target_meet_isIso p k n u f₂ hp₂) U

def sourceComparison : GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source Pairs S' Q ⟶
    ((S').mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.CechCone.Total.CechConeTotal.total U Q) :=
  GeometricComparison.Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} Pairs R S' Q
    (MorphismRowRestriction.source_meet_isIso p k n u f₁ hp₁) U

theorem natural : targetComparison p k n u f₂ hp₂ U ≫ totalSectionsMap p k n u v f₁ f₂ hp₁ hp₂ sq U =
    diagonalMap p k n u v f₁ f₂ hp₁ hp₂ sq ≫ sourceComparison p k n u f₁ hp₁ U :=
  GeometricComparison.Section.DiagonalCechChange.SectionDiagonalCechChange.natural.{0, 2, 1, 2, 1, 1, 2} Pairs R T S S' P Q a b
    (MorphismRowRestriction.target_meet_isIso p k n u f₂ hp₂)
    (MorphismRowRestriction.source_meet_isIso p k n u f₁ hp₁) U

theorem totalSectionsMap_eq : totalSectionsMap p k n u v f₁ f₂ hp₁ hp₂ sq U =
    GeometricComparison.Section.CochainPullback.SectionCochainPullback.map T S S' b (MorphismCech.map p k n u v f₁ f₂ hp₁ hp₂ sq U) :=
  GeometricComparison.CechCone.TotalSectionMap.CechConeTotalSectionMap.map_eq T S S' U P Q a b

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalCech
