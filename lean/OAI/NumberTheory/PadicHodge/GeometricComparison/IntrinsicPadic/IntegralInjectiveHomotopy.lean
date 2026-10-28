import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameInjectiveHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralSource

/-! # Integral Injective Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy

noncomputable section

/-! The original native integral quotient-to-injective comparison is
natural up to homotopy under actual geometric maps of integral models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

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
local notation "F₁" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u))
local notation "F₂" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u))
local notation "D₁" => F₁ ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₁ n
local notation "D₂" => F₂ ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₂ n

def sourceMap : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D₁ ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (F₁ ⋙ FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X₁ Y₁ f₁ hp₁ n) :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (Functor.whiskerLeft F₁
    (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X₁ Y₁ f₁ hp₁ n))

def targetMap : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D₂ ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (F₂ ⋙ FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X₂ Y₂ f₂ hp₂ n) :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (Functor.whiskerLeft F₂
    (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X₂ Y₂ f₂ hp₂ n))

def geometricMap : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D₂ ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D₁ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (IntegralSource.IntrinsicPadicGeometricIntegralSource.transformation p u n)

def sourceComparison := sourceMap p u f₁ hp₁ n ≫
  FrameInjectiveHomotopy.IntrinsicPadicGeometricFrameInjectiveHomotopy.sourceComparison p u f₁ hp₁ n I₁
def targetComparison := targetMap p u f₂ hp₂ n ≫
  FrameInjectiveHomotopy.IntrinsicPadicGeometricFrameInjectiveHomotopy.targetComparison p u f₂ hp₂ n I₂

omit [IsProper X₁.hom] [IsProper X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem frame_square : targetMap p u f₂ hp₂ n ≫ FrameDiagonal.IntrinsicPadicGeometricFrameDiagonal.map p u v f₁ f₂ hp₁ hp₂ hsquare n =
    geometricMap p u n ≫ sourceMap p u f₁ hp₁ n := by
  let A := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (T := (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) (V := ModuleCat.{2} R) (.up ℕ)
  exact (A.map_comp _ _).symm.trans
    ((congrArg A.map (IntegralSource.IntrinsicPadicGeometricIntegralSource.natural p u v f₁ f₂ hp₁ hp₂ hsquare n)).trans (A.map_comp _ _))

omit [IsProper X₂.hom] [Smooth X₂.hom] [IsSeparated Y₂.hom] in
theorem source_coordinates_component (q : ℕ) (U : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    (((((DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.sourcePullback p u).mapHomologicalComplex (.up ℕ)).map
      (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₁ Y₁ f₁ hp₁ n I₁)).f q).app U) =
      ((sourceComparison p u f₁ hp₁ n I₁).f q).app U := rfl

omit [IsProper X₁.hom] [Smooth X₁.hom] [IsSeparated Y₁.hom] in
theorem target_coordinates_component (q : ℕ) (U : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    (((((DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.targetPullback p u).mapHomologicalComplex (.up ℕ)).map
      (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂)).f q).app U) =
      ((targetComparison p u f₂ hp₂ n I₂).f q).app U := rfl

def homotopy : Homotopy
    (targetComparison p u f₂ hp₂ n I₂ ≫ SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (geometricMap p u n ≫ sourceComparison p u f₁ hp₁ n I₁) :=
  HomotopyPrecomposition.HomotopyPrecompositionSquare.homotopy (targetMap p u f₂ hp₂ n) (sourceMap p u f₁ hp₁ n)
    (FrameInjectiveHomotopy.IntrinsicPadicGeometricFrameInjectiveHomotopy.targetComparison p u f₂ hp₂ n I₂)
    (FrameInjectiveHomotopy.IntrinsicPadicGeometricFrameInjectiveHomotopy.sourceComparison p u f₁ hp₁ n I₁)
    (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (geometricMap p u n) (FrameDiagonal.IntrinsicPadicGeometricFrameDiagonal.map p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (FrameInjectiveHomotopy.IntrinsicPadicGeometricFrameInjectiveHomotopy.homotopy p u v f₁ f₂ hp₁ hp₂ hsquare n I₁ I₂)
    (frame_square p u v f₁ f₂ hp₁ hp₂ hsquare n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjectiveHomotopy.IntrinsicPadicGeometricIntegralInjectiveHomotopy
