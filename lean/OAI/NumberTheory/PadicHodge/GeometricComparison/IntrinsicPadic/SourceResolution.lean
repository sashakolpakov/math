import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinedCechSheafResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoverCech

/-! # Source Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SourceResolution.IntrinsicPadicGeometricSourceResolution

noncomputable section

/-! The source diagram on the common affine-pair cover is an actual
augmented resolution of the original crystalline structure sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  (u : X₁ ⟶ X₂) (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X₁.left)
  (hp : IsPullback f Y.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₁ Y f hp n
local notation "η" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X₁ Y f hp n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u)
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n

local instance sheafCoproducts : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W))
    (IntegralComparison.BoundedCrystalline.Site.topology w n)

def complex := CechCone.Total.CechConeTotal.total U ((F).op ⋙ P)
def augmentation : (CochainComplex.single₀ _).obj O ⟶ complex p u Y f hp n :=
  CechCone.Total.CechConeTotal.augmentation U ((F).op ⋙ P) _ (Functor.whiskerLeft (F).op η)

def projectionIso : complex p u Y f hp n ≅
    CechCone.Total.CechConeTotal.total (Cover.IntrinsicPadicGeometricCover.opens p u) P :=
  CechCone.TotalProductReindex.CechConeTotalProductReindex.iso F U P

theorem projection_augmentation : augmentation p u Y f hp n ≫ (projectionIso p u Y f hp n).hom =
    CechCone.Total.CechConeTotal.augmentation (Cover.IntrinsicPadicGeometricCover.opens p u) P _ η :=
  CechCone.TotalProductReindex.CechConeTotalProductReindex.augmentation F U P _ η

theorem augmentation_quasiIso : QuasiIso (augmentation p u Y f hp n) := by
  apply (quasiIso_iff_comp_right _ (projectionIso p u Y f hp n).hom).mp
  rw [projection_augmentation]
  exact RefinedCechSheafResolution.IntrinsicPadicRefinedCechSheafResolution.diagram_quasiIso p X₁ Y f hp n
    (Cover.IntrinsicPadicGeometricCover.opens p u) (Cover.IntrinsicPadicGeometricCover.sourceIndex p u)
    (Cover.IntrinsicPadicGeometricCover.le_source p u) (Cover.IntrinsicPadicGeometricCover.cover p u)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SourceResolution.IntrinsicPadicGeometricSourceResolution
