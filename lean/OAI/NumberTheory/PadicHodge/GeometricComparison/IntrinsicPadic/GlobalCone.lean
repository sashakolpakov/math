import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.TopCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex

/-! # Global Cone -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalCone.IntrinsicPadicGeometricGlobalCone

noncomputable section

/-! The actual geometric map on injective sections preserves the
original global-section cones on compatible integral affine pairs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  (I₁ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n))
  (I₂ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "Pairs" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.Charts (Over.Hom.left u)
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂
local notation "K₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.complex w₁ n I₁
local notation "K₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.complex w₂ n I₂

def sourceGlobal : CochainComplex (ModuleCat.{2} R) ℕ := (CechPresheaf.TopCone.CechPresheafTopCone.global Y₁.left.Opens).obj K₁
def targetGlobal : CochainComplex (ModuleCat.{2} R) ℕ := (CechPresheaf.TopCone.CechPresheafTopCone.global Y₂.left.Opens).obj K₂

def sourceCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Pairs)).obj (sourceGlobal p n I₁) ⟶
    ((SectionMap.IntrinsicPadicGeometricSectionMap.sourceSections p u f₁ n).mapHomologicalComplex (.up ℕ)).obj I₁.cocomplex :=
  ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R)
    (OpenPairs.IntrinsicPadicGeometricOpenPairs.source p u f₁)).mapHomologicalComplex (.up ℕ)).map
      (CechPresheaf.TopCone.CechPresheafTopCone.cone Y₁.left.Opens K₁)

def targetCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Pairs)).obj (targetGlobal p n I₂) ⟶
    ((SectionMap.IntrinsicPadicGeometricSectionMap.targetSections p u f₂ n).mapHomologicalComplex (.up ℕ)).obj I₂.cocomplex :=
  ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R)
    (OpenPairs.IntrinsicPadicGeometricOpenPairs.target p u f₂)).mapHomologicalComplex (.up ℕ)).map
      (CechPresheaf.TopCone.CechPresheafTopCone.cone Y₂.left.Opens K₂)

def globalMap : targetGlobal p n I₂ ⟶ sourceGlobal p n I₁ :=
  Bounded.OpenCohomology.BoundedGeometricOpenCohomology.map v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n I₂ I₁

omit [Smooth X₁.hom] [Smooth X₂.hom] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem component (q : ℕ) (U : Pairsᵒᵖ) :
    ((targetCone p u f₂ n I₂).f q).app U ≫
      ((SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂).f q).app U =
    (globalMap p v n I₁ I₂).f q ≫ ((sourceCone p u f₁ n I₁).f q).app U := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [Smooth X₁.hom] [Smooth X₂.hom] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem naturality : targetCone p u f₂ n I₂ ≫
    SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂ =
      (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Pairs)).map (globalMap p v n I₁ I₂) ≫ sourceCone p u f₁ n I₁ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext U
  exact component p u v f₁ f₂ hsquare n I₁ I₂ q U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalCone.IntrinsicPadicGeometricGlobalCone
