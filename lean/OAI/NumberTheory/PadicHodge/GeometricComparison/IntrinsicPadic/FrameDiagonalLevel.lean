import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameOpenLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexDiagonal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalCechLevel

/-! # Frame Diagonal Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalLevel.IntrinsicPadicFrameDiagonalLevel

noncomputable section

/-! The original native frame-to-diagonal comparison commutes with
the actual level transition after assembling the presheaf complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)

local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp
local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp
local notation "d" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameSourceLevelMap.IntrinsicPadicFrameSourceLevelMap.transformation p X Y f hp n m hnm

def map : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (D m) ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (D n) :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) d

def diagonalTransformation : BifunctorDiagonalEq.BifunctorDiagonal.functor (SectionBifunctor.IntrinsicPadicSectionBifunctor.rows p X Y f hp m) ⟶
    BifunctorDiagonalEq.BifunctorDiagonal.functor (SectionBifunctor.IntrinsicPadicSectionBifunctor.rows p X Y f hp n) :=
  BifunctorDiagonalApp.BifunctorDiagonalMap.map (SectionLevelMap.IntrinsicPadicSectionLevelMap.rows p X Y f n m hnm hp)

omit [X.left.IsSeparated] in
theorem transformation : FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.transformation p X Y f hp m ≫
    diagonalTransformation p X Y f hp n m hnm =
      d ≫ FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.transformation p X Y f hp n := by
  apply NatTrans.ext
  funext V
  apply HomologicalComplex.Hom.ext
  funext i
  let am := (((FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp m).app V).f i).app V
  let an := (((FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp n).app V).f i).app V
  let b := (((SectionLevelMap.IntrinsicPadicSectionLevelMap.complexes p X Y f n m hnm hp).app V).f i).app V
  have h := congrArg (fun q => ((q.app V).f i).app V) (FrameOpenLevel.IntrinsicPadicFrameOpenLevel.natural p X Y f hp n m hnm)
  change am ≫ b = ((d).app V).f i ≫ an at h
  change (am ≫ 𝟙 _) ≫ b = ((d).app V).f i ≫ (an ≫ 𝟙 _)
  exact (congrArg (fun q => q ≫ b) (Category.comp_id am)).trans
    (h.trans (congrArg (fun q => ((d).app V).f i ≫ q) (Category.comp_id an).symm))

theorem natural : FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.map p X Y f hp m ≫
    DiagonalCechLevel.IntrinsicPadicDiagonalCechLevel.diagonalMap p X Y f hp n m hnm =
      IntrinsicPadicFrameDiagonalLevel.map p X Y f hp n m hnm ≫ FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.map p X Y f hp n := by
  let A := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (T := X.left.affineOpensᵒᵖ)
    (V := ModuleCat.{2} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p)))) (.up ℕ)
  exact (A.map_comp _ _).symm.trans
    ((congrArg A.map (transformation p X Y f hp n m hnm)).trans (A.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalLevel.IntrinsicPadicFrameDiagonalLevel
