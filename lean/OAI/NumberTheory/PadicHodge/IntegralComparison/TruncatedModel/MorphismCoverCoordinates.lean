import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOrdinaryCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoverOrdinaryCech

/-! # Morphism Cover Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoverCoordinates

noncomputable section

/-! The paired ordinary de Rham diagrams use the actual source and
target affine-cover complexes, with scalar restriction explicit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "F₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u)
local notation "F₂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u)
local notation "G" => ModuleCat.restrictScalars (algebraMap (WittVector p k) R)
local notation "GC" => Functor.mapHomologicalComplex G (ComplexShape.up ℕ)

local instance source_products (j : ℕ)
    (t : Fin (j + 1) → MorphismCover.Index p k n u) :
    PreservesLimit (Discrete.functor (U ∘ t)) (F₁ ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X₁.left) :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (F₁ ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X₁.left) (fun _ _ => rfl) (U ∘ t)

local instance target_products (j : ℕ)
    (t : Fin (j + 1) → MorphismCover.Index p k n u) :
    PreservesLimit (Discrete.functor (U ∘ t)) (F₂ ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X₂.left) :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (F₂ ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X₂.left) (fun _ _ => rfl) (U ∘ t)

def sourceCover : MorphismCover.Index p k n u → X₁.left.affineOpens :=
  (F₁).obj ∘ U

def targetCover : MorphismCover.Index p k n u → X₂.left.affineOpens :=
  (F₂).obj ∘ U

def sourceNative := IntrinsicDeRham.CechComplex.Intrinsic.total R X₁
  (Affine.CoverDeRhamUnit.opens R X₁ (sourceCover p k n u))

def targetNative := IntrinsicDeRham.CechComplex.Intrinsic.total R X₂
  (Affine.CoverDeRhamUnit.opens R X₂ (targetCover p k n u))

omit [Fintype k] [CharP k p] in
private theorem finiteIndices (m : SimplexCategory) : Finite ((N).obj (op m)).I := by
  change Finite (Fin (m.len + 1) → MorphismCover.Index p k n u)
  infer_instance

def sourceBaseIso :=
  IndexedOrdinaryCech.Ordinary.totalIso R X₁ (F₁ ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X₁.left) U ≪≫
    Affine.CoverDeRhamUnit.totalIso R X₁ (sourceCover p k n u)
      (MorphismCover.sourceIndex p k n u)
      (MorphismCover.le_source p k n u)

def targetBaseIso :=
  IndexedOrdinaryCech.Ordinary.totalIso R X₂ (F₂ ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X₂.left) U ≪≫
    Affine.CoverDeRhamUnit.totalIso R X₂ (targetCover p k n u)
      (MorphismCover.targetIndex p k n u) (fun _ => le_rfl)

def sourceIso :
    GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total N
      (Functor.op F₁ ⋙ OrdinaryBaseIso.Ordinary.target p k n X₁) ≅
        (GC).obj (sourceNative p k n u) :=
  (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G N (finiteIndices p k n u)
    (Functor.op F₁ ⋙ Small.OrdinaryCechTotal.Ordinary.diagram R X₁)).symm ≪≫
      (GC).mapIso (sourceBaseIso p k n u)

def targetIso :
    GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total N
      (Functor.op F₂ ⋙ OrdinaryBaseIso.Ordinary.target p k n X₂) ≅
        (GC).obj (targetNative p k n u) :=
  (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G N (finiteIndices p k n u)
    (Functor.op F₂ ⋙ Small.OrdinaryCechTotal.Ordinary.diagram R X₂)).symm ≪≫
      (GC).mapIso (targetBaseIso p k n u)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoverCoordinates
