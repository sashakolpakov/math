import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameOpen
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexDiagonal

/-! # Frame Diagonal -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonal.IntrinsicPadicGeometricFrameDiagonal

noncomputable section

/-! The native geometric frame square descends to the diagonal section
complex and its assembled presheaf cochain map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [Smooth X₁.hom] [Smooth X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "Pairs" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.Charts (Over.Hom.left u)
local notation "D" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X₂ Y₂ f₂ hp₂ n
local notation "D'" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X₁ Y₁ f₁ hp₁ n
local notation "P" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₂ Y₂ f₂ hp₂ n
local notation "Q" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u)) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X₁ Y₁ f₁ hp₁ n
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.targetSections p u f₂ n
local notation "S'" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.sourceSections p u f₁ n
local notation "d" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameSource.IntrinsicPadicGeometricFrameSource.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n

local instance constPreservesZero :
    (Functor.const (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ : ModuleCat.{2} Rcoeff ⥤
      (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def targetTransformation : D ⟶ BifunctorDiagonalEq.BifunctorDiagonal.functor
    (RowRestriction.IntrinsicPadicGeometricRowRestriction.targetRows p u f₂ hp₂ n) :=
  Functor.whiskerLeft (Affine.MapPairs.AffineMapPairs.target u.left).op
    (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.transformation p X₂ Y₂ f₂ hp₂ n)

def sourceTransformation : D' ⟶ BifunctorDiagonalEq.BifunctorDiagonal.functor
    (RowRestriction.IntrinsicPadicGeometricRowRestriction.sourceRows p u f₁ hp₁ n) :=
  Functor.whiskerLeft (Affine.MapPairs.AffineMapPairs.source u.left).op
    (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.transformation p X₁ Y₁ f₁ hp₁ n)

def diagonalTransformation : BifunctorDiagonalEq.BifunctorDiagonal.functor
    (RowRestriction.IntrinsicPadicGeometricRowRestriction.targetRows p u f₂ hp₂ n) ⟶ BifunctorDiagonalEq.BifunctorDiagonal.functor
      (RowRestriction.IntrinsicPadicGeometricRowRestriction.sourceRows p u f₁ hp₁ n) :=
  BifunctorDiagonalApp.BifunctorDiagonalMap.map (SectionMap.IntrinsicPadicGeometricSectionMap.rows p u v f₁ f₂ hsquare n hp₁ hp₂)

omit [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem transformation : targetTransformation p u f₂ hp₂ n ≫ diagonalTransformation p u v f₁ f₂ hp₁ hp₂ hsquare n =
    d ≫ sourceTransformation p u f₁ hp₁ n := by
  apply NatTrans.ext
  funext V
  apply HomologicalComplex.Hom.ext
  funext i
  let am := (((FrameOpen.IntrinsicPadicGeometricFrameOpen.targetOpen p u f₂ hp₂ n).app V).f i).app V
  let an := (((FrameOpen.IntrinsicPadicGeometricFrameOpen.sourceOpen p u f₁ hp₁ n).app V).f i).app V
  let b := (((SectionMap.IntrinsicPadicGeometricSectionMap.complexes p u v f₁ f₂ hsquare n hp₁ hp₂).app V).f i).app V
  have h := FrameOpen.IntrinsicPadicGeometricFrameOpen.component p u v f₁ f₂ hp₁ hp₂ hsquare n V.unop V.unop i
  change am ≫ b = ((d).app V).f i ≫ an at h
  change (am ≫ 𝟙 _) ≫ b = ((d).app V).f i ≫ (an ≫ 𝟙 _)
  exact (congrArg (fun q => q ≫ b) (Category.comp_id am)).trans
    (h.trans (congrArg (fun q => ((d).app V).f i ≫ q) (Category.comp_id an).symm))

def targetMap : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D ⟶ Section.DiagonalCone.SectionDiagonalCone.source Pairs S P :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (targetTransformation p u f₂ hp₂ n)
def sourceMap : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D' ⟶ Section.DiagonalCone.SectionDiagonalCone.source Pairs S' Q :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (sourceTransformation p u f₁ hp₁ n)
def map : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D' :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) d

theorem natural : targetMap p u f₂ hp₂ n ≫ DiagonalCech.IntrinsicPadicGeometricDiagonalCech.diagonalMap p u v f₁ f₂ hp₁ hp₂ hsquare n =
    IntrinsicPadicGeometricFrameDiagonal.map p u v f₁ f₂ hp₁ hp₂ hsquare n ≫ sourceMap p u f₁ hp₁ n := by
  let A := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (T := Pairsᵒᵖ) (V := ModuleCat.{2} Rcoeff) (.up ℕ)
  exact (A.map_comp _ _).symm.trans
    ((congrArg A.map (transformation p u v f₁ f₂ hp₁ hp₂ hsquare n)).trans (A.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonal.IntrinsicPadicGeometricFrameDiagonal
