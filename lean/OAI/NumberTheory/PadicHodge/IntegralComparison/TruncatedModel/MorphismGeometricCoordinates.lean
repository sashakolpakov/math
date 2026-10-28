import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.MorphismIntrinsicCechTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoverCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinedCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedCoefficientCoordinateSquare

/-! # Morphism Geometric Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometricCoordinates

noncomputable section

/-! The common-cover map used by the original bounded crystalline
comparison is the actual geometric pullback on native de Rham totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X₂
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "F₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left
local notation "F₂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left
local notation "D₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechTotal.Ordinary.diagram R X₁
local notation "D₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechTotal.Ordinary.diagram R X₂
local notation "G" => ModuleCat.restrictScalars (algebraMap (WittVector p k) R)
local notation "GC" => Functor.mapHomologicalComplex G (ComplexShape.up ℕ)
local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement.target p k n u

local instance products (j : ℕ)
    (t : Fin (j + 1) → MorphismCover.Index p k n u) :
    PreservesLimit (Discrete.functor (U ∘ t)) F₂ :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves F₂ (fun _ _ => rfl) (U ∘ t)

omit [Fintype k] [CharP k p] in
private theorem finiteIndices (m : SimplexCategory) : Finite ((N).obj (op m)).I := by
  change Finite (Fin (m.len + 1) → MorphismCover.Index p k n u)
  infer_instance

def map : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total R X₂ ⟶
    MorphismCoverCoordinates.sourceNative p k n u :=
  Affine.MorphismIntrinsicCechTotal.Intrinsic.map R u U V r

abbrev refinement_coefficients := GeometricComparison.CechAssembly.RefinedCoefficient.CechAssemblyRefinedCoefficient.total F₂ G U V r D₂

abbrev geometric_coefficients := GeometricComparison.CechAssembly.CoefficientNaturality.CechAssemblyCoefficientNaturality.natural G N
  (finiteIndices p k n u) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.transformation R u)

abbrev geometric_native := Affine.MorphismIntrinsicCechTotal.Intrinsic.total R u U V r
  (MorphismCover.sourceIndex p k n u)
  (MorphismCover.le_source p k n u) id (fun _ => le_rfl)

abbrev total := RefinedCoefficientCoordinateSquare.square GC
  (Affine.MorphismOrdinaryCechTotal.Ordinary.refinement R u U V r)
  (Affine.MorphismOrdinaryCechTotal.Ordinary.geometricMap R u U)
  (MorphismCoverCoordinates.sourceBaseIso p k n u)
  (Small.OrdinaryCechTotal.Ordinary.totalIso R X₂)
  (map p k n u)
  (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G (NonemptyCechNerve.nerve V)
    (Small.OrdinaryCechTotal.Ordinary.finiteIndices R X₂) D₂)
  (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G N (finiteIndices p k n u) (Functor.op F₂ ⋙ D₂))
  (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G N (finiteIndices p k n u) (Functor.op F₁ ⋙ D₁))
  (MorphismOrdinaryCech.Ordinary.targetOrdinaryRefinement p k n u)
  (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u)
  (refinement_coefficients p k n u)
  (geometric_coefficients p k n u)
  (geometric_native p k n u)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometricCoordinates
