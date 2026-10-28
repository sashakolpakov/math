import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.SectionGlobalCoordinates

/-! # Morphism Global Refinement Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementCoordinates

noncomputable section

/-! Component coordinates for the actual old and common-cover
bounded section edges. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "F₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u)
local notation "F₂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u)
local notation "S₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.specialOpens p k n X₁ Y₁ f₁
local notation "S₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.specialOpens p k n X₂ Y₂ f₂

abbrev source_old_component (q : ℕ) := GeometricComparison.Bounded.SectionGlobalCoordinates.BoundedSectionGlobalCoordinates.component w₁ n I₁ S₁
  (CechSliceResolution.opens p k n X₁) q
abbrev target_old_component (q : ℕ) := GeometricComparison.Bounded.SectionGlobalCoordinates.BoundedSectionGlobalCoordinates.component w₂ n I₂ S₂
  (CechSliceResolution.opens p k n X₂) q

omit [Fintype k] [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated] [IsSeparated Y₁.hom] in
theorem source_cone_component (q : ℕ) (V : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ) :
    ((GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.newCone w₁ n I₁ F₁ S₁).f q).app V =
      ((MorphismGlobalCone.sourceCone p k n u f₁ I₁).f q).app V := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [Fintype k] [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated] [IsSeparated Y₂.hom] in
theorem target_cone_component (q : ℕ) (V : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ) :
    ((GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.newCone w₂ n I₂ F₂ S₂).f q).app V =
      ((MorphismGlobalCone.targetCone p k n u f₂ I₂).f q).app V := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

abbrev source_new_component (q : ℕ) := GeometricComparison.CechPresheaf.ConeComponentCongr.CechPresheafConeComponentCongr.component U
  (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.newSections w₁ n I₁ F₁ S₁)
  (MorphismGlobalCone.sourceGlobal p k n I₁)
  (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.newCone w₁ n I₁ F₁ S₁)
  (MorphismGlobalCone.sourceCone p k n u f₁ I₁) q
  (source_cone_component p k n u f₁ I₁ q)

abbrev target_new_component (q : ℕ) := GeometricComparison.CechPresheaf.ConeComponentCongr.CechPresheafConeComponentCongr.component U
  (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.newSections w₂ n I₂ F₂ S₂)
  (MorphismGlobalCone.targetGlobal p k n I₂)
  (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.newCone w₂ n I₂ F₂ S₂)
  (MorphismGlobalCone.targetCone p k n u f₂ I₂) q
  (target_cone_component p k n u f₂ I₂ q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementCoordinates
