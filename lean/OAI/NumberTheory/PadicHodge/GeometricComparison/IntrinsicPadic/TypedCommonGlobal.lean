import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CommonHomologyMaps

/-! # Typed Common Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal

noncomputable section

/-! A common global comparison defined from the actual typed
common edge and the original global section comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  (I₁ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n))
  (I₂ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasLimitsOfSize.{0, 0, 2, 1}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasColimitsOfSize.{2, 1, 0, 0} R

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GeometricCone.IntrinsicPadicGeometricConeTotalMaps

local instance source_edge_iso : IsIso (CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.source_common p u f₁ n I₁) := by
  let : QuasiIso (CommonGlobal.IntrinsicPadicGeometricCommonGlobal.sourceEdge p u f₁ n I₁) :=
    CommonGlobal.IntrinsicPadicGeometricCommonGlobal.source_quasiIso p u f₁ n I₁
  exact inferInstanceAs (IsIso (HomologicalComplex.homologyMap
    (CommonGlobal.IntrinsicPadicGeometricCommonGlobal.sourceEdge p u f₁ n I₁) 1))

def global : ModuleCat.{2} R := ModuleCat.of R
  (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n 1)

def globalMap : (ConeSectionData.IntrinsicPadicGeometricConeSectionData.sourceGlobal p n I₁).homology 1 ⟶
    global p n (Y₁ := Y₁) :=
  (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n I₁ 1).hom

def comparison : (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceNew p u f₁ n I₁).homology 1 ⟶ global p n (Y₁ := Y₁) :=
  inv (CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.source_common p u f₁ n I₁) ≫ globalMap p n I₁

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem homology : CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.source_common p u f₁ n I₁ ≫
    comparison p u f₁ n I₁ = globalMap p n I₁ := by
  dsimp only [comparison]
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal
