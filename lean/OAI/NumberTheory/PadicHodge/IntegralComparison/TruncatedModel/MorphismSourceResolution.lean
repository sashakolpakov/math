import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.RefinedSheafResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement

/-! # Morphism Source Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceResolution

noncomputable section

/-! The common source cover supplies an actual augmented resolution of the original bounded crystalline structure sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  (u : X₁ ⟶ X₂)
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X₁.left)
  (hp : IsPullback f Y.hom X₁.hom (Spec.map (CommRingCat.ofHom
    (Truncated.Witt.reduction p k n))))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₁ Y f hp
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.augmentation p k n X₁ Y f hp
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u)
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := γ) w n
local instance sheafCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : WittVector p k)}) (δ := γ) w n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (BoundedCrystalline.Site.topology w n)
def complex := GeometricComparison.CechCone.Total.CechConeTotal.total U ((F).op ⋙ P)
def augmentation : (CochainComplex.single₀ _).obj O ⟶ complex p k n u Y f hp :=
  GeometricComparison.CechCone.Total.CechConeTotal.augmentation U ((F).op ⋙ P) _ (Functor.whiskerLeft (F).op η)
def projectionIso : complex p k n u Y f hp ≅ GeometricComparison.CechCone.Total.CechConeTotal.total (MorphismCover.opens p k n u) P :=
  GeometricComparison.CechCone.TotalProductReindex.CechConeTotalProductReindex.iso F U P

theorem projection_augmentation : augmentation p k n u Y f hp ≫ (projectionIso p k n u Y f hp).hom =
    GeometricComparison.CechCone.Total.CechConeTotal.augmentation (MorphismCover.opens p k n u) P _ η :=
  GeometricComparison.CechCone.TotalProductReindex.CechConeTotalProductReindex.augmentation F U P _ η

theorem augmentation_quasiIso : QuasiIso (augmentation p k n u Y f hp) := by
  apply (quasiIso_iff_comp_right _ (projectionIso p k n u Y f hp).hom).mp
  rw [projection_augmentation]
  exact RefinedSheafResolution.diagram_quasiIso p k n X₁ Y f hp
    (MorphismCover.opens p k n u) (MorphismCover.sourceIndex p k n u)
    (MorphismCover.le_source p k n u) (MorphismCover.cover p k n u)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceResolution
