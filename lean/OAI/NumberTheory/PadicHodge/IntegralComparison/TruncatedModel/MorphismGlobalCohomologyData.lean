import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.RefinedGlobal

/-! # Morphism Global Cohomology Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomologyData

noncomputable section

/-! Original global-edge epimorphisms and geometric naturality on cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

variable (q : ℕ)
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "e₁" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.edge p k n X₁ Y₁ f₁ I₁) q
local notation "e₂" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.edge p k n X₂ Y₂ f₂ I₂) q
local notation "r₁" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.sourceMap p k n u f₁ I₁) q
local notation "r₂" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.targetMap p k n u f₂ I₂) q
local notation "p₁" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.sourceEdge p k n u f₁ I₁) q
local notation "p₂" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.targetEdge p k n u f₂ I₂) q
local notation "a" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCone.globalMap p k n v I₁ I₂) q
local notation "b" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.geometricMap p k n u v f₁ f₂ sq I₁ I₂) q
local notation "g" => ModuleCat.ofHom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback v.left (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames.ambient_over p k v) n q)
local notation "i₁" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.InjectiveCech.homologyIso p k n X₁ Y₁ f₁ I₁ q)
local notation "i₂" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.InjectiveCech.homologyIso p k n X₂ Y₂ f₂ I₂ q)
local notation "h" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.sourceHomologyIso p k n u f₁ I₁ q)
local notation "j₁" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal.homologyIso w₁ n I₁ q)
local notation "j₂" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal.homologyIso w₂ n I₂ q)
local instance sourceEdgeEpi : Epi e₁ := by
  let : QuasiIso (GlobalEdge.edge p k n X₁ Y₁ f₁ I₁) := GlobalEdge.quasiIso p k n X₁ Y₁ f₁ I₁
  infer_instance
local instance targetEdgeEpi : Epi e₂ := by
  let : QuasiIso (GlobalEdge.edge p k n X₂ Y₂ f₂ I₂) := GlobalEdge.quasiIso p k n X₂ Y₂ f₂ I₂
  infer_instance

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
omit [Fintype k] in
theorem geometric_edge : p₂ ≫ b = a ≫ p₁ :=
  (HomologicalComplex.homologyMap_comp _ _ q).symm.trans
    ((congrArg (fun m => HomologicalComplex.homologyMap m q)
      (MorphismCommonGlobal.naturality p k n u v f₁ f₂ sq I₁ I₂)).trans
        (HomologicalComplex.homologyMap_comp _ _ q))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomologyData
