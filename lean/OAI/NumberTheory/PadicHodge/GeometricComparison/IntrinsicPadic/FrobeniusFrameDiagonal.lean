import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameOpen
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexDiagonal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusDiagonalCech

/-! # Frobenius Frame Diagonal -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameDiagonal.IntrinsicPadicFrobeniusFrameDiagonal

noncomputable section

/-! The original native frame-to-diagonal comparison commutes with
actual level-zero Frobenius after assembling the presheaf complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))

local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp
local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp
local notation "d" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameSource.IntrinsicPadicFrobeniusFrameSource.transformation p X Y f hp

def map : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (D 0) ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (D 0) :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) d

def diagonalTransformation : BifunctorDiagonalEq.BifunctorDiagonal.functor (SectionBifunctor.IntrinsicPadicSectionBifunctor.rows p X Y f hp 0) ⟶
    BifunctorDiagonalEq.BifunctorDiagonal.functor (SectionBifunctor.IntrinsicPadicSectionBifunctor.rows p X Y f hp 0) :=
  BifunctorDiagonalApp.BifunctorDiagonalMap.map (FrobeniusSectionMap.IntrinsicPadicFrobeniusSectionMap.rows p X Y f hp)

omit [X.left.IsSeparated] in
theorem transformation : FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.transformation p X Y f hp 0 ≫
    diagonalTransformation p X Y f hp =
      d ≫ FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.transformation p X Y f hp 0 := by
  apply NatTrans.ext
  funext V
  apply HomologicalComplex.Hom.ext
  funext i
  let am := (((FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp 0).app V).f i).app V
  let an := (((FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp 0).app V).f i).app V
  let b := (((FrobeniusSectionMap.IntrinsicPadicFrobeniusSectionMap.complexes p X Y f hp).app V).f i).app V
  have h := congrArg (fun q => ((q.app V).f i).app V) (FrobeniusFrameOpen.IntrinsicPadicFrobeniusFrameOpen.natural p X Y f hp)
  change am ≫ b = ((d).app V).f i ≫ an at h
  change (am ≫ 𝟙 _) ≫ b = ((d).app V).f i ≫ (an ≫ 𝟙 _)
  exact (congrArg (fun q => q ≫ b) (Category.comp_id am)).trans
    (h.trans (congrArg (fun q => ((d).app V).f i ≫ q) (Category.comp_id an).symm))

theorem natural : FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.map p X Y f hp 0 ≫
    FrobeniusDiagonalCech.IntrinsicPadicFrobeniusDiagonalCech.diagonalMap p X Y f hp =
      IntrinsicPadicFrobeniusFrameDiagonal.map p X Y f hp ≫ FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.map p X Y f hp 0 := by
  let A := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (T := X.left.affineOpensᵒᵖ)
    (V := ModuleCat.{2} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p)))) (.up ℕ)
  exact (A.map_comp _ _).symm.trans
    ((congrArg A.map (transformation p X Y f hp)).trans (A.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameDiagonal.IntrinsicPadicFrobeniusFrameDiagonal
