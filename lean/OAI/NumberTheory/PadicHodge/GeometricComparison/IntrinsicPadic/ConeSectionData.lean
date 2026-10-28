import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinementConeCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedReferenceEdgeCoordinates

/-! # Cone Section Data -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ConeSectionData.IntrinsicPadicGeometricTypedReferenceEdgeComponents

/-! The original inverse global edge agrees in degree one with
the literal native cone edge used for refinement. -/
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

/- Each intermediate component has the original native Hom type. The
coordinate changes are checked separately before composing their proofs. -/
def sourceCanonicalComponent :
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.global p Y₁ n I₁).X 1 ⟶
      (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.source p X₁ Y₁ f₁ n I₁).X 1 :=
  (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.edge p X₁ Y₁ f₁ n I₁).f 1

def sourceRefinementComponent :
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.global p Y₁ n I₁).X 1 ⟶
      (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.source p X₁ Y₁ f₁ n I₁).X 1 :=
  (RefinementConeCoordinates.IntrinsicPadicGeometricRefinementConeCoordinates.sourceOldEdge p f₁ n I₁).f 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_original_coordinates : (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.edge p X₁ Y₁ f₁ n I₁).f 1 =
    sourceCanonicalComponent p f₁ n I₁ :=
  TypedReferenceEdgeCoordinates.IntrinsicPadicTypedReferenceEdgeCoordinates.edge_component p X₁ Y₁ f₁ n I₁ 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_refinement_coordinates : sourceCanonicalComponent p f₁ n I₁ =
    sourceRefinementComponent p f₁ n I₁ :=
  RefinementConeCoordinates.IntrinsicPadicGeometricRefinementConeCoordinates.source_old_component p f₁ n I₁ 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_edge_component : (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.edge p X₁ Y₁ f₁ n I₁).f 1 =
    (RefinementConeCoordinates.IntrinsicPadicGeometricRefinementConeCoordinates.sourceOldEdge p f₁ n I₁).f 1 :=
  (source_original_coordinates p f₁ n I₁).trans (source_refinement_coordinates p f₁ n I₁)

def targetCanonicalComponent :
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.global p Y₂ n I₂).X 1 ⟶
      (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.source p X₂ Y₂ f₂ n I₂).X 1 :=
  (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.edge p X₂ Y₂ f₂ n I₂).f 1

def targetRefinementComponent :
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.global p Y₂ n I₂).X 1 ⟶
      (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.source p X₂ Y₂ f₂ n I₂).X 1 :=
  (RefinementConeCoordinates.IntrinsicPadicGeometricRefinementConeCoordinates.targetOldEdge p f₂ n I₂).f 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_original_coordinates : (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.edge p X₂ Y₂ f₂ n I₂).f 1 =
    targetCanonicalComponent p f₂ n I₂ :=
  TypedReferenceEdgeCoordinates.IntrinsicPadicTypedReferenceEdgeCoordinates.edge_component p X₂ Y₂ f₂ n I₂ 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_refinement_coordinates : targetCanonicalComponent p f₂ n I₂ =
    targetRefinementComponent p f₂ n I₂ :=
  RefinementConeCoordinates.IntrinsicPadicGeometricRefinementConeCoordinates.target_old_component p f₂ n I₂ 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_edge_component : (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.edge p X₂ Y₂ f₂ n I₂).f 1 =
    (RefinementConeCoordinates.IntrinsicPadicGeometricRefinementConeCoordinates.targetOldEdge p f₂ n I₂).f 1 :=
  (target_original_coordinates p f₂ n I₂).trans (target_refinement_coordinates p f₂ n I₂)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ConeSectionData.IntrinsicPadicGeometricTypedReferenceEdgeComponents

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ConeSectionData.IntrinsicPadicGeometricConeSectionData

/-! Fix the original global complex and old and new section-cone
map types before forming any Cech total or homology object. -/
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

def sourceOldSections : CochainComplex (X₁.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ℕ :=
  GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.sections p X₁ Y₁ f₁ n I₁

def sourceNewSections : CochainComplex ((Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} R) ℕ :=
  ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (Affine.MapPairs.AffineMapPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj
    (sourceOldSections p f₁ n I₁)

def sourceGlobal : CochainComplex (ModuleCat.{2} R) ℕ :=
  GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.global p Y₁ n I₁

def sourceOldCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₁.left.affineOpens)).obj
    (sourceGlobal p n I₁) ⟶ sourceOldSections p f₁ n I₁ :=
  GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.cone p X₁ Y₁ f₁ n I₁

def sourceNewCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Affine.MapPairs.AffineMapPairs.Charts u.left)).obj
    (sourceGlobal p n I₁) ⟶ sourceNewSections p u f₁ n I₁ :=
  GlobalCone.IntrinsicPadicGeometricGlobalCone.sourceCone p u f₁ n I₁

def sourcePulledCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Affine.MapPairs.AffineMapPairs.Charts u.left)).obj
    (sourceGlobal p n I₁) ⟶ sourceNewSections p u f₁ n I₁ :=
  CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (Affine.MapPairs.AffineMapPairs.source u.left)
    (sourceOldSections p f₁ n I₁) (sourceGlobal p n I₁) (sourceOldCone p f₁ n I₁)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem source_component (W : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    ((sourcePulledCone p u f₁ n I₁).f 1).app W = ((sourceNewCone p u f₁ n I₁).f 1).app W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (RefinementConeCoordinates.IntrinsicPadicGeometricRefinementConeCoordinates.source_cone_component p u f₁ n I₁ 1 W) x

def targetOldSections : CochainComplex (X₂.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ℕ :=
  GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.sections p X₂ Y₂ f₂ n I₂

def targetNewSections : CochainComplex ((Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} R) ℕ :=
  ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (Affine.MapPairs.AffineMapPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj
    (targetOldSections p f₂ n I₂)

def targetGlobal : CochainComplex (ModuleCat.{2} R) ℕ :=
  GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.global p Y₂ n I₂

def targetOldCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₂.left.affineOpens)).obj
    (targetGlobal p n I₂) ⟶ targetOldSections p f₂ n I₂ :=
  GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.cone p X₂ Y₂ f₂ n I₂

def targetNewCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Affine.MapPairs.AffineMapPairs.Charts u.left)).obj
    (targetGlobal p n I₂) ⟶ targetNewSections p u f₂ n I₂ :=
  GlobalCone.IntrinsicPadicGeometricGlobalCone.targetCone p u f₂ n I₂

def targetPulledCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := Affine.MapPairs.AffineMapPairs.Charts u.left)).obj
    (targetGlobal p n I₂) ⟶ targetNewSections p u f₂ n I₂ :=
  CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (Affine.MapPairs.AffineMapPairs.target u.left)
    (targetOldSections p f₂ n I₂) (targetGlobal p n I₂) (targetOldCone p f₂ n I₂)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem target_component (W : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    ((targetPulledCone p u f₂ n I₂).f 1).app W = ((targetNewCone p u f₂ n I₂).f 1).app W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (RefinementConeCoordinates.IntrinsicPadicGeometricRefinementConeCoordinates.target_cone_component p u f₂ n I₂ 1 W) x

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ConeSectionData.IntrinsicPadicGeometricConeSectionData

end

end OAI
