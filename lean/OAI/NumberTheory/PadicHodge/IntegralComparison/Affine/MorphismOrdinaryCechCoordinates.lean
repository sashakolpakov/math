import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryPullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryProjectedReindex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairProducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.TotalFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.RefinementCoordinate

/-! # Morphism Ordinary Cech Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.MorphismOrdinaryCechCoordinates.Ordinary

noncomputable section

/-! The actual ordinary map on affine pairs gives the
actual geometric Cech pullback after the original coordinate isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (R : Type u) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} [X.left.IsSeparated] [Y.left.IsSeparated]
  (f : X ⟶ Y)
  {ι κ : Type} (U : ι → AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts f.left) (V : κ → Y.left.affineOpens)
  (r : FormalCoproduct.mk ι ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left).obj ∘ U) ⟶ FormalCoproduct.mk κ V)

local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.sourceOpens R f
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.targetOpens R f
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left
local notation "H" => Functor.mapHomologicalComplex
  (NonemptyCechNerve.complexFunctor (A := ModuleCat R) U) (ComplexShape.up ℕ)
local notation "a" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (ComplexShape.up ℕ) (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.transformation R f)
local notation "e₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryCech.Ordinary.complexIso R X S
local notation "e₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryCech.Ordinary.complexIso R Y T
local notation "b" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ProjectedCechComplexPullback.SmallProjectedCechComplexPullback.pairedMap R (Over.Hom.left f) T S
  (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryPullback.AffineMorphismOrdinaryPullback.openMap R f) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.presheafPullback f)

local instance source_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t))
      (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source f.left ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source f.left ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) (fun _ _ => rfl) (U ∘ t)

local instance target_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t))
      (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left) :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left) (fun _ _ => rfl) (U ∘ t)

local instance source_opens_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.sourceOpens R f) :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.sourceOpens R f) (fun _ _ => rfl) (U ∘ t)

local instance target_opens_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t)) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.targetOpens R f) :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryForms.AffineMorphismOrdinaryForms.targetOpens R f) (fun _ _ => rfl) (U ∘ t)

local instance cover_preserves (n : ℕ) (t : Fin (n + 1) → κ) :
    PreservesLimit (Discrete.functor (V ∘ t)) (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left) :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.inclusion_preserves Y.left (V ∘ t)

local instance projected_cover_preserves (n : ℕ) (t : Fin (n + 1) → ι) :
    PreservesLimit
      (Discrete.functor (((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left).obj ∘ U) ∘ t))
      (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left) :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.inclusion_preserves Y.left
    (((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left).obj ∘ U) ∘ t)

omit [X.left.IsSeparated] [Y.left.IsSeparated] in
theorem complex_square : a ≫ (e₁).hom = (e₂).hom ≫ b :=
  ((e₂).hom_inv_id_assoc (a ≫ (e₁).hom)).symm.trans
    (congrArg (fun c => (e₂).hom ≫ c) (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryPullback.AffineMorphismOrdinaryPullback.coordinates R f))

def refinement := GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left) U V r
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IndexedOrdinaryCech.Ordinary.diagram R Y G))

def geometricMap := (H).map a

def openRefinement := GeometricComparison.NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G
  ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left).obj ∘ U) V r

def directMap := AlgebraicGeometry.Crystalline.Cohomology.RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.bicomplexMap R f.left ((G).obj ∘ V) ((S).obj ∘ U)
  (openRefinement R f U V r).f
  (AlgebraicGeometry.Crystalline.Cohomology.SmallProjectedLE.SmallProjectedCechPullback.coverLE f.left T S (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryPullback.AffineMorphismOrdinaryPullback.openMap R f)
    U ((G).obj ∘ V) (openRefinement R f U V r))
  (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.presheafPullback f)

def projectedRefinement := GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap T U ((G).obj ∘ V)
  (openRefinement R f U V r) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y )

def projectedGeometry := (H).map b ≫
  (GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso S U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X )).hom

theorem geometric_coordinates : geometricMap R f  U ≫
    (IndexedOrdinaryCech.Ordinary.bicomplexIso R X S U ).hom =
      (H).map (e₂).hom ≫ projectedGeometry R f  U := by
  have hc : (H).map a ≫ (H).map (e₁).hom = (H).map (e₂).hom ≫ (H).map b :=
    ((H).map_comp _ _).symm.trans
      ((congrArg (H).map (complex_square R f )).trans ((H).map_comp _ _))
  let P := (GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso S U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X )).hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun c => c ≫ P) hc).trans (Category.assoc _ _ _))

theorem refinement_coordinates : refinement R f  U V r ≫ (H).map (e₂).hom =
    (IndexedOrdinaryCech.Ordinary.bicomplexIso R Y G V).hom ≫ projectedRefinement R f  U V r :=
  IndexedOrdinaryProjectedReindex.Ordinary.bicomplex R Y
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left) G U V  r

theorem pullback_coordinates : projectedRefinement R f  U V r ≫ projectedGeometry R f  U =
    directMap R f  U V r :=
  AlgebraicGeometry.Crystalline.Cohomology.ProjectedCechComplexPullback.SmallProjectedCechComplexPullback.comparison R f.left T S
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismOrdinaryPullback.AffineMorphismOrdinaryPullback.openMap R f) U ((G).obj ∘ V) (openRefinement R f U V r)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.presheafPullback f)

theorem bicomplex : refinement R f  U V r ≫ geometricMap R f  U ≫
    (IndexedOrdinaryCech.Ordinary.bicomplexIso R X S U ).hom =
      (IndexedOrdinaryCech.Ordinary.bicomplexIso R Y G V).hom ≫ directMap R f  U V r :=
  GeometricComparison.RefinementCoordinate.RefinementCoordinateSquare.square _ _ _ _ _ _ _ _
    (geometric_coordinates R f  U) (refinement_coordinates R f  U V r) (pullback_coordinates R f  U V r)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.MorphismOrdinaryCechCoordinates.Ordinary
