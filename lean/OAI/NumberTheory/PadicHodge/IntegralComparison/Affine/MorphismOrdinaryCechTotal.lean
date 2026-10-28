import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.MorphismOrdinaryCechCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.TripleSquare

/-! # Morphism Ordinary Cech Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.MorphismOrdinaryCechTotal.Ordinary

noncomputable section

/-! Original affine total coordinates preserve the actual
geometric pullback through the common affine-pair cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (R : Type u) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} [X.left.IsSeparated] [Y.left.IsSeparated]
  (f : X ⟶ Y)
  {ι κ : Type} (U : ι → AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts f.left) (V : κ → Y.left.affineOpens)
  (r : FormalCoproduct.mk ι ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left).obj ∘ U) ⟶ FormalCoproduct.mk κ V)

local instance source_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.sourceOpens R f) :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.sourceOpens R f) (fun _ _ => rfl) (U ∘ t)

local instance cover_preserves (n : ℕ) (t : Fin (n + 1) → κ) :
    PreservesLimit (Discrete.functor (V ∘ t)) (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left) :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.inclusion_preserves Y.left (V ∘ t)

def refinement := HomologicalComplex₂.total.map
  (MorphismOrdinaryCechCoordinates.Ordinary.refinement R f  U V r) (.up ℕ)
def geometricMap := HomologicalComplex₂.total.map
  (MorphismOrdinaryCechCoordinates.Ordinary.geometricMap R f  U) (.up ℕ)
def sourceIso := HomologicalComplex₂.total.mapIso
  (IndexedOrdinaryCech.Ordinary.bicomplexIso R X (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.sourceOpens R f) U ) (.up ℕ)
def targetIso := HomologicalComplex₂.total.mapIso (IndexedOrdinaryCech.Ordinary.bicomplexIso R Y (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left) V) (.up ℕ)
def directMap := HomologicalComplex₂.total.map (MorphismOrdinaryCechCoordinates.Ordinary.directMap R f  U V r) (.up ℕ)

theorem total : refinement R f  U V r ≫ geometricMap R f  U ≫ (sourceIso R f  U).hom =
    (targetIso R  V).hom ≫ directMap R f  U V r :=
  GeometricComparison.Functor.TripleSquare.FunctorTripleSquare.square
    (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (.up ℕ) (.up ℕ) (.up ℕ))
    (MorphismOrdinaryCechCoordinates.Ordinary.refinement R f  U V r)
    (MorphismOrdinaryCechCoordinates.Ordinary.geometricMap R f  U)
    (IndexedOrdinaryCech.Ordinary.bicomplexIso R X (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.sourceOpens R f) U ).hom
    (IndexedOrdinaryCech.Ordinary.bicomplexIso R Y (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left) V).hom
    (MorphismOrdinaryCechCoordinates.Ordinary.directMap R f  U V r)
    (MorphismOrdinaryCechCoordinates.Ordinary.bicomplex R f  U V r)

theorem refinement_component (q : ℕ) : (GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left) U V r
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IndexedOrdinaryCech.Ordinary.diagram R Y (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left)))).f q =
      (refinement R f  U V r).f q := rfl

theorem geometric_component (q : ℕ) :
    ((GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor (NonemptyCechNerve.nerve U)).map
      (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.transformation R f)).f q = (geometricMap R f  U).f q := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.MorphismOrdinaryCechTotal.Ordinary
