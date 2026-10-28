import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.TopCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex

/-! # Morphism Global Cone -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCone

noncomputable section

/-! The actual geometric map on injective sections preserves the
original global-section cones on compatible integral affine pairs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

local instance coefficientRing : Ring R := (inferInstance : CommRing R).toRing

local notation "Pairs" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts (Over.Hom.left u)
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "K₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.complex w₁ n I₁
local notation "K₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.complex w₂ n I₂

def sourceGlobal : CochainComplex (ModuleCat.{2} R) ℕ := (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.global Y₁.left.Opens).obj K₁
def targetGlobal : CochainComplex (ModuleCat.{2} R) ℕ := (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.global Y₂.left.Opens).obj K₂

def sourceCone : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Pairs)).obj (sourceGlobal p k n I₁) ⟶
    ((MorphismSectionMap.sourceSections p k n u f₁).mapHomologicalComplex (.up ℕ)).obj I₁.cocomplex :=
  ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R)
    (MorphismOpenPairs.source p k n u f₁)).mapHomologicalComplex (.up ℕ)).map
      (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone Y₁.left.Opens K₁)

def targetCone : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Pairs)).obj (targetGlobal p k n I₂) ⟶
    ((MorphismSectionMap.targetSections p k n u f₂).mapHomologicalComplex (.up ℕ)).obj I₂.cocomplex :=
  ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R)
    (MorphismOpenPairs.target p k n u f₂)).mapHomologicalComplex (.up ℕ)).map
      (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone Y₂.left.Opens K₂)

def globalMap : targetGlobal p k n I₂ ⟶ sourceGlobal p k n I₁ :=
  GeometricComparison.Bounded.OpenCohomology.BoundedGeometricOpenCohomology.map v.left (MorphismData.Frames.ambient_over p k v) n I₂ I₁

omit [Smooth X₁.hom] [Smooth X₂.hom] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
omit [Fintype k] in
theorem component (q : ℕ) (U : Pairsᵒᵖ) :
    ((targetCone p k n u f₂ I₂).f q).app U ≫
      ((MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂).f q).app U =
    (globalMap p k n v I₁ I₂).f q ≫ ((sourceCone p k n u f₁ I₁).f q).app U := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [Smooth X₁.hom] [Smooth X₂.hom] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
omit [Fintype k] in
theorem naturality : targetCone p k n u f₂ I₂ ≫
    MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂ =
      (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Pairs)).map (globalMap p k n v I₁ I₂) ≫ sourceCone p k n u f₁ I₁ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext U
  exact component p k n u v f₁ f₂ sq I₁ I₂ q U

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCone
