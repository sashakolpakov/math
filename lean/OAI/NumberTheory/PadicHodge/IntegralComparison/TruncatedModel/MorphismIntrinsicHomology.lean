import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Morphism Intrinsic Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicHomology.Intrinsic

noncomputable section

/-! Exact coefficient change carries the actual common-cover
refinement and geometric pullback squares to cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.coefficientFunctor p k

def sourceIso (i : ℕ) := GeometricComparison.ExactHomology.ExactHomologyComparison.iso G (.up ℕ) _ _
  (MorphismIntrinsicCoordinates.Intrinsic.sourceIso p k n f₁ hp₁) i

def targetIso (i : ℕ) := GeometricComparison.ExactHomology.ExactHomologyComparison.iso G (.up ℕ) _ _
  (MorphismIntrinsicCoordinates.Intrinsic.targetIso p k n f₂ hp₂) i

def commonSourceIso (i : ℕ) := GeometricComparison.ExactHomology.ExactHomologyComparison.iso G (.up ℕ) _ _
  (MorphismCoefficientCech.ordinarySourceIso p k n u f₁ hp₁) i

def commonTargetIso (i : ℕ) := GeometricComparison.ExactHomology.ExactHomologyComparison.iso G (.up ℕ) _ _
  (MorphismCoefficientCech.ordinaryTargetIso p k n u f₂ hp₂) i

abbrev source (i : ℕ) := GeometricComparison.ExactHomology.ExactHomologyComparison.naturality G (.up ℕ)
  (MorphismIntrinsicCoordinates.Intrinsic.sourceIso p k n f₁ hp₁)
  (MorphismCoefficientCech.ordinarySourceIso p k n u f₁ hp₁)
  (MorphismIntrinsicCoordinates.Intrinsic.sourceMap p k n u)
  (MorphismCoefficientCech.sourceRefinement p k n u f₁ hp₁)
  (MorphismIntrinsicCoordinates.Intrinsic.source p k n u f₁ hp₁).symm i

abbrev target (i : ℕ) := GeometricComparison.ExactHomology.ExactHomologyComparison.naturality G (.up ℕ)
  (MorphismIntrinsicCoordinates.Intrinsic.targetIso p k n f₂ hp₂)
  (MorphismCoefficientCech.ordinaryTargetIso p k n u f₂ hp₂)
  (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u)
  (MorphismCoefficientCech.targetRefinement p k n u f₂ hp₂)
  (MorphismIntrinsicCoordinates.Intrinsic.target p k n u f₂ hp₂).symm i

abbrev geometric (i : ℕ) := GeometricComparison.ExactHomology.ExactHomologyComparison.naturality G (.up ℕ)
  (MorphismCoefficientCech.ordinaryTargetIso p k n u f₂ hp₂)
  (MorphismCoefficientCech.ordinarySourceIso p k n u f₁ hp₁)
  (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u)
  (MorphismCoefficientCech.geometricMap p k n u v f₁ f₂ hp₁ hp₂ sq)
  (MorphismCoefficientCech.ordinary_natural p k n u v f₁ f₂ hp₁ hp₂ sq) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicHomology.Intrinsic
