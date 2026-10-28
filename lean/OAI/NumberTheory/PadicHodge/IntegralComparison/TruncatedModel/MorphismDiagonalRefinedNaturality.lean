import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback

/-! # Morphism Diagonal Refined Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalRefinedNaturality

noncomputable section

/-! The original chosen-cover diagonal maps commute with the actual
geometric map into the common refined source resolution. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Over.Hom.left v) (MorphismData.Frames.ambient_over p k v) n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.targetSections p k n u f₂
local notation "S'" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.sourceSections p k n u f₁
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.transformation p k n u v f₁ f₂ sq
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinedResolution.targetRefinement p k n u f₂ hp₂
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCech.map p k n u v f₁ f₂ hp₁ hp₂ sq U
local notation "totalMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalCech.totalSectionsMap p k n u v f₁ f₂ hp₁ hp₂ sq U

theorem target_factor : MorphismSectionHomotopy.targetMap p k n u v f₁ f₂ hp₁ hp₂ sq =
    ((S).mapHomologicalComplex (.up ℕ)).map r ≫ totalMap :=
  (GeometricComparison.Section.CochainPullback.SectionCochainPullbackFactorization.precompose T S S' b r a).symm.trans
    (congrArg (fun q => ((S).mapHomologicalComplex (.up ℕ)).map r ≫ q)
      (MorphismDiagonalCech.totalSectionsMap_eq p k n u v f₁ f₂ hp₁ hp₂ sq U).symm)

theorem natural : MorphismDiagonalRefinement.targetMap p k n u f₂ hp₂ ≫
    MorphismSectionHomotopy.targetMap p k n u v f₁ f₂ hp₁ hp₂ sq =
      MorphismDiagonalCech.diagonalMap p k n u v f₁ f₂ hp₁ hp₂ sq ≫
        MorphismDiagonalRefinement.sourceMap p k n u f₁ hp₁ ≫
          MorphismSectionHomotopy.sourceMap p k n u f₁ hp₁ :=
  (congrArg (fun q => MorphismDiagonalRefinement.targetMap p k n u f₂ hp₂ ≫ q)
    (target_factor p k n u v f₁ f₂ hp₁ hp₂ sq)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ totalMap)
          (MorphismDiagonalRefinement.target_comparison p k n u f₂ hp₂)).trans
            ((MorphismDiagonalCech.natural p k n u v f₁ f₂ hp₁ hp₂ sq U).trans
              (congrArg (fun q => MorphismDiagonalCech.diagonalMap p k n u v f₁ f₂ hp₁ hp₂ sq ≫ q)
                (MorphismDiagonalRefinement.source_comparison p k n u f₁ hp₁).symm))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalRefinedNaturality
