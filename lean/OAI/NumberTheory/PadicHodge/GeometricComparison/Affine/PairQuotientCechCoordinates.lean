import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairQuotientPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryQuotientProjectedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairProducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.TotalFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.RefinementCoordinate

/-! # Pair Quotient Cech Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairQuotientCechCoordinates.AffinePairQuotientCechCoordinates

noncomputable section

/-! The actual ordinary quotient map on affine pairs gives the
original geometric Cech pullback after the original coordinate isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} [X.left.IsSeparated] [Y.left.IsSeparated]
  (f : X ⟶ Y) (I : Ideal R)
  {ι κ : Type} (U : ι → MapPairs.AffineMapPairs.Charts f.left) (V : κ → Y.left.affineOpens)
  (r : FormalCoproduct.mk ι ((MapPairs.AffineMapPairs.target f.left).obj ∘ U) ⟶ FormalCoproduct.mk κ V)

local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens R f
local notation "T" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryForms.AffinePairOrdinaryForms.targetOpens R f
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left
local notation "H" => Functor.mapHomologicalComplex
  (IntegralComparison.NonemptyCechNerve.complexFunctor (A := ModuleCat R) U) (ComplexShape.up ℕ)
local notation "a" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (ComplexShape.up ℕ) (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairQuotientPullback.AffinePairQuotientPullback.transformation R f I)
local notation "e₁" => OAI.NumberTheory.PadicHodge.GeometricComparison.IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.complexIso R X S I
local notation "e₂" => OAI.NumberTheory.PadicHodge.GeometricComparison.IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.complexIso R Y T I
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectedCechTotal.ProjectedCechComplexPullback.pairedMap R (Over.Hom.left f) T S
  (PairOrdinaryPullback.AffinePairOrdinaryPullback.openMap R f) (PairQuotientPullback.AffinePairQuotientPullback.originalMap R f I)

local instance source_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t))
      (MapPairs.AffineMapPairs.source f.left ⋙ OpenProducts.AffineOpenProducts.inclusion X.left) :=
  Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (MapPairs.AffineMapPairs.source f.left ⋙ OpenProducts.AffineOpenProducts.inclusion X.left) (fun _ _ => rfl) (U ∘ t)

local instance target_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t))
      (MapPairs.AffineMapPairs.target f.left ⋙ OpenProducts.AffineOpenProducts.inclusion Y.left) :=
  Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (MapPairs.AffineMapPairs.target f.left ⋙ OpenProducts.AffineOpenProducts.inclusion Y.left) (fun _ _ => rfl) (U ∘ t)

local instance source_opens_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t)) (PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens R f) :=
  Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens R f) (fun _ _ => rfl) (U ∘ t)

local instance target_opens_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t)) (PairOrdinaryForms.AffinePairOrdinaryForms.targetOpens R f) :=
  Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (PairOrdinaryForms.AffinePairOrdinaryForms.targetOpens R f) (fun _ _ => rfl) (U ∘ t)

omit [X.left.IsSeparated] [Y.left.IsSeparated] in
theorem complex_square : a ≫ (e₁).hom = (e₂).hom ≫ b :=
  ((e₂).hom_inv_id_assoc (a ≫ (e₁).hom)).symm.trans
    (congrArg (fun c => (e₂).hom ≫ c) (PairQuotientPullback.AffinePairQuotientPullback.coordinates R f I))

def refinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap (MapPairs.AffineMapPairs.target f.left) U V r
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.diagram R Y I))

def geometricMap := (H).map a

def openRefinement := NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G
  ((MapPairs.AffineMapPairs.target f.left).obj ∘ U) V r

def directMap := Cech.ComplexPullback.CechPullback.bicomplexMap R f.left ((G).obj ∘ V) ((S).obj ∘ U)
  (openRefinement R f U V r).f
  (ProjectedCechLE.ProjectedCechPullback.coverLE f.left T S (PairOrdinaryPullback.AffinePairOrdinaryPullback.openMap R f)
    U ((G).obj ∘ V) (openRefinement R f U V r))
  (PairQuotientPullback.AffinePairQuotientPullback.originalMap R f I)

def projectedRefinement := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap T U ((G).obj ∘ V)
  (openRefinement R f U V r) (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R Y I)

def projectedGeometry := (H).map b ≫
  (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso S U (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R X I)).hom

theorem geometric_coordinates : geometricMap R f I U ≫
    (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.bicomplexIso R X S U I).hom =
      (H).map (e₂).hom ≫ projectedGeometry R f I U := by
  have hc : (H).map a ≫ (H).map (e₁).hom = (H).map (e₂).hom ≫ (H).map b :=
    ((H).map_comp _ _).symm.trans
      ((congrArg (H).map (complex_square R f I)).trans ((H).map_comp _ _))
  let P := (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso S U (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R X I)).hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun c => c ≫ P) hc).trans (Category.assoc _ _ _))

theorem refinement_coordinates : refinement R f I U V r ≫ (H).map (e₂).hom =
    (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.bicomplexIso R Y V I).hom ≫ projectedRefinement R f I U V r :=
  OrdinaryQuotientProjectedReindex.IndexedOrdinaryQuotientProjectedReindex.bicomplex R Y
    (MapPairs.AffineMapPairs.target f.left) G U V I r

theorem pullback_coordinates : projectedRefinement R f I U V r ≫ projectedGeometry R f I U =
    directMap R f I U V r :=
  ProjectedCechTotal.ProjectedCechComplexPullback.comparison R f.left T S
    (PairOrdinaryPullback.AffinePairOrdinaryPullback.openMap R f) U ((G).obj ∘ V) (openRefinement R f U V r)
    (PairQuotientPullback.AffinePairQuotientPullback.originalMap R f I)

theorem bicomplex : refinement R f I U V r ≫ geometricMap R f I U ≫
    (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.bicomplexIso R X S U I).hom =
      (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.bicomplexIso R Y V I).hom ≫ directMap R f I U V r :=
  RefinementCoordinate.RefinementCoordinateSquare.square _ _ _ _ _ _ _ _
    (geometric_coordinates R f I U) (refinement_coordinates R f I U V r) (pullback_coordinates R f I U V r)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairQuotientCechCoordinates.AffinePairQuotientCechCoordinates
