import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback

/-! # Diagonal Refined Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalRefinedNaturality.IntrinsicPadicGeometricDiagonalRefinedNaturality

noncomputable section

/-! The original chosen-cover diagonal maps commute with the actual
geometric map into the common refined source resolution. -/

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

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Over.Hom.left v) (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.targetSections p u f₂ n
local notation "S'" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.sourceSections p u f₁ n
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.transformation p u v f₁ f₂ hsquare n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u
local notation "r" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinedResolution.IntrinsicPadicGeometricRefinedResolution.targetRefinement p u f₂ hp₂ n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechDiagram.IntrinsicPadicGeometricCechDiagram.map p u v f₁ f₂ hp₁ hp₂ hsquare n U
local notation "totalMap" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalCech.IntrinsicPadicGeometricDiagonalCech.totalSectionsMap p u v f₁ f₂ hp₁ hp₂ hsquare n U

theorem target_factor : SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.targetMap p u v f₁ f₂ hp₁ hp₂ hsquare n =
    ((S).mapHomologicalComplex (.up ℕ)).map r ≫ totalMap :=
  (Section.CochainPullback.SectionCochainPullbackFactorization.precompose T S S' b r a).symm.trans
    (congrArg (fun q => ((S).mapHomologicalComplex (.up ℕ)).map r ≫ q)
      (DiagonalCech.IntrinsicPadicGeometricDiagonalCech.totalSectionsMap_eq p u v f₁ f₂ hp₁ hp₂ hsquare n U).symm)

theorem natural : DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.targetMap p u f₂ hp₂ n ≫
    SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.targetMap p u v f₁ f₂ hp₁ hp₂ hsquare n =
      DiagonalCech.IntrinsicPadicGeometricDiagonalCech.diagonalMap p u v f₁ f₂ hp₁ hp₂ hsquare n ≫
        DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.sourceMap p u f₁ hp₁ n ≫
          SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.sourceMap p u f₁ hp₁ n :=
  (congrArg (fun q => DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.targetMap p u f₂ hp₂ n ≫ q)
    (target_factor p u v f₁ f₂ hp₁ hp₂ hsquare n)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ totalMap)
          (DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.target_comparison p u f₂ hp₂ n)).trans
            ((DiagonalCech.IntrinsicPadicGeometricDiagonalCech.natural p u v f₁ f₂ hp₁ hp₂ hsquare n U).trans
              (congrArg (fun q => DiagonalCech.IntrinsicPadicGeometricDiagonalCech.diagonalMap p u v f₁ f₂ hp₁ hp₂ hsquare n ≫ q)
                (DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.source_comparison p u f₁ hp₁ n).symm))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalRefinedNaturality.IntrinsicPadicGeometricDiagonalRefinedNaturality
