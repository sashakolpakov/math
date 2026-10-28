import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairQuotientCechCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.TripleSquare

/-! # Pair Quotient Cech Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairQuotientCechTotal.AffinePairQuotientCechTotal

noncomputable section

/-! Original affine quotient total coordinates preserve the actual
geometric pullback through the common affine-pair cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} [X.left.IsSeparated] [Y.left.IsSeparated]
  (f : X ⟶ Y) (I : Ideal R)
  {ι κ : Type} (U : ι → MapPairs.AffineMapPairs.Charts f.left) (V : κ → Y.left.affineOpens)
  (r : FormalCoproduct.mk ι ((MapPairs.AffineMapPairs.target f.left).obj ∘ U) ⟶ FormalCoproduct.mk κ V)

local instance source_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t)) (PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens R f) :=
  Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens R f) (fun _ _ => rfl) (U ∘ t)

def refinement := HomologicalComplex₂.total.map
  (PairQuotientCechCoordinates.AffinePairQuotientCechCoordinates.refinement R f I U V r) (.up ℕ)
def geometricMap := HomologicalComplex₂.total.map
  (PairQuotientCechCoordinates.AffinePairQuotientCechCoordinates.geometricMap R f I U) (.up ℕ)
def sourceIso := HomologicalComplex₂.total.mapIso
  (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.bicomplexIso R X (PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens R f) U I) (.up ℕ)
def targetIso := HomologicalComplex₂.total.mapIso (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.bicomplexIso R Y V I) (.up ℕ)
def directMap := HomologicalComplex₂.total.map (PairQuotientCechCoordinates.AffinePairQuotientCechCoordinates.directMap R f I U V r) (.up ℕ)

theorem total : refinement R f I U V r ≫ geometricMap R f I U ≫ (sourceIso R f I U).hom =
    (targetIso R I V).hom ≫ directMap R f I U V r :=
  Functor.TripleSquare.FunctorTripleSquare.square
    (HomologicalComplex₂.totalFunctor (ModuleCat.{0} R) (.up ℕ) (.up ℕ) (.up ℕ))
    (PairQuotientCechCoordinates.AffinePairQuotientCechCoordinates.refinement R f I U V r)
    (PairQuotientCechCoordinates.AffinePairQuotientCechCoordinates.geometricMap R f I U)
    (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.bicomplexIso R X (PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens R f) U I).hom
    (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.bicomplexIso R Y V I).hom
    (PairQuotientCechCoordinates.AffinePairQuotientCechCoordinates.directMap R f I U V r)
    (PairQuotientCechCoordinates.AffinePairQuotientCechCoordinates.bicomplex R f I U V r)

theorem refinement_component (q : ℕ) : (CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map (MapPairs.AffineMapPairs.target f.left) U V r
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.diagram R Y I))).f q =
      (refinement R f I U V r).f q := rfl

theorem geometric_component (q : ℕ) :
    ((CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor (IntegralComparison.NonemptyCechNerve.nerve U)).map
      (PairQuotientPullback.AffinePairQuotientPullback.transformation R f I)).f q = (geometricMap R f I U).f q := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairQuotientCechTotal.AffinePairQuotientCechTotal
