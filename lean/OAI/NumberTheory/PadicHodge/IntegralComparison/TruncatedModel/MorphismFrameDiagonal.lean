import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameOpen
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexDiagonal

/-! # Morphism Frame Diagonal -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameDiagonal

noncomputable section

/-! The native geometric frame square descends to the diagonal section
complex and its assembled presheaf cochain map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

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

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "Pairs" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts (Over.Hom.left u)
local notation "D" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalMap.source p k n X₂ Y₂ f₂ hp₂
local notation "D'" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁
local notation "P" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₂ Y₂ f₂ hp₂
local notation "Q" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X₁ Y₁ f₁ hp₁
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.targetSections p k n u f₂
local notation "S'" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.sourceSections p k n u f₁
local notation "d" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameSource.transformation p k n u v f₁ f₂ hp₁ hp₂ sq

local instance constPreservesZero :
    (Functor.const (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ : ModuleCat.{2} Rcoeff ⥤
      (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def targetTransformation : D ⟶ GeometricComparison.BifunctorDiagonalEq.BifunctorDiagonal.functor
    (MorphismRowRestriction.targetRows p k n u f₂ hp₂) :=
  Functor.whiskerLeft (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op
    (FrameDiagonalMap.transformation p k n X₂ Y₂ f₂ hp₂)

def sourceTransformation : D' ⟶ GeometricComparison.BifunctorDiagonalEq.BifunctorDiagonal.functor
    (MorphismRowRestriction.sourceRows p k n u f₁ hp₁) :=
  Functor.whiskerLeft (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op
    (FrameDiagonalMap.transformation p k n X₁ Y₁ f₁ hp₁)

def diagonalTransformation : GeometricComparison.BifunctorDiagonalEq.BifunctorDiagonal.functor
    (MorphismRowRestriction.targetRows p k n u f₂ hp₂) ⟶ GeometricComparison.BifunctorDiagonalEq.BifunctorDiagonal.functor
      (MorphismRowRestriction.sourceRows p k n u f₁ hp₁) :=
  GeometricComparison.BifunctorDiagonalApp.BifunctorDiagonalMap.map (MorphismSectionMap.rows p k n u v f₁ f₂ sq hp₁ hp₂)

omit [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem transformation : targetTransformation p k n u f₂ hp₂ ≫ diagonalTransformation p k n u v f₁ f₂ hp₁ hp₂ sq =
    d ≫ sourceTransformation p k n u f₁ hp₁ := by
  apply NatTrans.ext
  funext V
  apply HomologicalComplex.Hom.ext
  funext i
  let am := (((MorphismFrameOpen.targetOpen p k n u f₂ hp₂).app V).f i).app V
  let an := (((MorphismFrameOpen.sourceOpen p k n u f₁ hp₁).app V).f i).app V
  let b := (((MorphismSectionMap.complexes p k n u v f₁ f₂ sq hp₁ hp₂).app V).f i).app V
  have h := MorphismFrameOpen.component p k n u v f₁ f₂ hp₁ hp₂ sq V.unop V.unop i
  change am ≫ b = ((d).app V).f i ≫ an at h
  change (am ≫ 𝟙 _) ≫ b = ((d).app V).f i ≫ (an ≫ 𝟙 _)
  simpa only [Category.comp_id] using h

def targetMap : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D ⟶ GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source Pairs S P :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (targetTransformation p k n u f₂ hp₂)
def sourceMap : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D' ⟶ GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source Pairs S' Q :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (sourceTransformation p k n u f₁ hp₁)
def map : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D' :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) d

theorem natural : targetMap p k n u f₂ hp₂ ≫ MorphismDiagonalCech.diagonalMap p k n u v f₁ f₂ hp₁ hp₂ sq =
    MorphismFrameDiagonal.map p k n u v f₁ f₂ hp₁ hp₂ sq ≫ sourceMap p k n u f₁ hp₁ := by
  let A := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (T := Pairsᵒᵖ) (V := ModuleCat.{2} Rcoeff) (.up ℕ)
  exact (A.map_comp _ _).symm.trans
    ((congrArg A.map (transformation p k n u v f₁ f₂ hp₁ hp₂ sq)).trans (A.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameDiagonal
