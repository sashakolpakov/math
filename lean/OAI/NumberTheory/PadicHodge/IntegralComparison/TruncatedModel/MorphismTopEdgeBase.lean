import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.MorphismIntrinsicCechTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdgeMap

/-! # Morphism Top Edge Base -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdgeBase

noncomputable section

/-! The original common-cover top-form groups and their literal
ordinary de Rham pullback, independent of crystalline comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  (u : X₁ ⟶ X₂)
  (g : ℕ) [SmoothOfRelativeDimension g X₁.hom] [SmoothOfRelativeDimension g X₂.hom]
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X₂
local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement.target p k n u

def sourceCover := Affine.MorphismIntrinsicCechTotal.Intrinsic.sourceOpens R u U

def targetCover := AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X₂

def bicomplexMap := Affine.MorphismIntrinsicCechTotal.Intrinsic.bicomplexMap R u U V r

abbrev SourceTopForms := IntrinsicDeRham.TopEdge.Intrinsic.source R X₁ (sourceCover p k n u) g

abbrev TargetTopForms := IntrinsicDeRham.TopEdge.Intrinsic.source R X₂ (targetCover p k n (X₂ := X₂)) g

def pullback : TargetTopForms p k n (X₂ := X₂) g →ₗ[R] SourceTopForms p k n u g :=
  IntrinsicDeRham.TopEdgeMap.Intrinsic.rowMap R X₁ X₂
    (sourceCover p k n u) (targetCover p k n (X₂ := X₂)) g (bicomplexMap p k n u)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdgeBase
