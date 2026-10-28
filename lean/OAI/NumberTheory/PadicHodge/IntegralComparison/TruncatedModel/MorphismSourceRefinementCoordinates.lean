import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoverCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinedCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedCoefficientCoordinateSquare

/-! # Morphism Source Refinement Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementCoordinates

noncomputable section

/-! The genuine refinement from the small source cover to the
common source cover has the same ordinary and coefficient coordinates
as the original model comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X₁
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left
local notation "J" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X₁.left
local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement.source p k n u
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechTotal.Ordinary.diagram R X₁
local notation "G" => ModuleCat.restrictScalars (algebraMap (WittVector p k) R)
local notation "GC" => Functor.mapHomologicalComplex G (ComplexShape.up ℕ)

local instance source_products (j : ℕ)
    (t : Fin (j+1) → MorphismCover.Index p k n u) :
    PreservesLimit (Discrete.functor (U ∘ t)) F :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves F (fun _ _ => rfl) (U ∘ t)

local instance source_open_products (j : ℕ)
    (t : Fin (j+1) → MorphismCover.Index p k n u) :
    PreservesLimit (Discrete.functor (U ∘ t)) (F ⋙ J) :=
  GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves (F ⋙ J) (fun _ _ => rfl) (U ∘ t)

local instance source_inclusion_products (j : ℕ)
    (t : Fin (j+1) → MorphismCover.Index p k n u) :
    PreservesLimit (Discrete.functor (((F).obj ∘ U) ∘ t)) J :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.inclusion_preserves X₁.left (((F).obj ∘ U) ∘ t)

local instance small_inclusion_products (j : ℕ)
    (t : Fin (j+1) → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X₁) :
    PreservesLimit (Discrete.functor (V ∘ t)) J :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.inclusion_preserves X₁.left (V ∘ t)

def openRefinement := GeometricComparison.NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover J ((F).obj ∘ U) V r

def map : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total R X₁ ⟶
    MorphismCoverCoordinates.sourceNative p k n u :=
  IntrinsicDeRham.CoverRefinement.Intrinsic.map R X₁ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X₁)
    (Affine.CoverDeRhamUnit.opens R X₁
      (MorphismCoverCoordinates.sourceCover p k n u))
    (openRefinement p k n u)

def ordinaryMap := GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D)

omit [Fintype k] [CharP k p] [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
private theorem bicomplex_native :
    GeometricComparison.CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.bicomplexMap (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X₁)
      (Affine.CoverDeRhamUnit.opens R X₁
        (MorphismCoverCoordinates.sourceCover p k n u))
      (openRefinement p k n u) (AlgebraicGeometry.Crystalline.Cohomology.Base.ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness.presheafComplex R X₁) =
    IntrinsicDeRham.CoverRefinement.Intrinsic.bicomplexMap R X₁ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X₁)
      (Affine.CoverDeRhamUnit.opens R X₁
        (MorphismCoverCoordinates.sourceCover p k n u))
      (openRefinement p k n u) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply HomologicalComplex.Hom.ext
  funext j
  rfl

omit [Fintype k] [CharP k p] [X₂.left.IsSeparated] in
private theorem units :
    GeometricComparison.CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.map (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X₁)
      (Affine.CoverDeRhamUnit.opens R X₁
        (MorphismCoverCoordinates.sourceCover p k n u))
      (openRefinement p k n u) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X₁) ≫
      (Affine.CoverDeRhamUnit.totalIso R X₁
        (MorphismCoverCoordinates.sourceCover p k n u)
        (MorphismCover.sourceIndex p k n u)
        (MorphismCover.le_source p k n u)).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.totalIso R X₁).hom ≫ MorphismSourceRefinementCoordinates.map p k n u := by
  have h := ((GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.transformation
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X₁)
    (Affine.CoverDeRhamUnit.opens R X₁
      (MorphismCoverCoordinates.sourceCover p k n u))
    (openRefinement p k n u)).mapHomologicalComplex (.up ℕ)).naturality
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.unit R X₁)
  have hh := congrArg (fun b => HomologicalComplex₂.total.map b (.up ℕ)) h.symm
  simp only [HomologicalComplex₂.total.map_comp] at hh
  have hn := congrArg (fun b => HomologicalComplex₂.total.map b (.up ℕ))
    (bicomplex_native p k n u)
  exact hh.trans (congrArg (fun b => (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.totalIso R X₁).hom ≫ b) hn)

omit [Fintype k] [CharP k p] in
theorem ordinary_coordinates :
    ordinaryMap p k n u ≫ (MorphismCoverCoordinates.sourceBaseIso p k n u).hom =
      (Small.OrdinaryCechTotal.Ordinary.totalIso R X₁).hom ≫ MorphismSourceRefinementCoordinates.map p k n u :=
  GeometricComparison.ExactHomology.ExactHomologyComparison.compose
    (ordinaryMap p k n u)
    (IndexedOrdinaryCech.Ordinary.totalIso R X₁ (F ⋙ J) U).hom
    (Affine.CoverDeRhamUnit.totalIso R X₁
      (MorphismCoverCoordinates.sourceCover p k n u)
      (MorphismCover.sourceIndex p k n u)
      (MorphismCover.le_source p k n u)).hom
    (IndexedOrdinaryCech.Ordinary.totalIso R X₁ J V).hom
    (GeometricComparison.CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.map (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X₁)
      (Affine.CoverDeRhamUnit.opens R X₁
        (MorphismCoverCoordinates.sourceCover p k n u))
      (openRefinement p k n u) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X₁))
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.totalIso R X₁).hom (MorphismSourceRefinementCoordinates.map p k n u)
    (IndexedOrdinaryReindex.Ordinary.total R X₁ F J U V r) (units p k n u)

omit [Fintype k] [CharP k p] in
theorem coordinates :
    MorphismIntrinsicCoordinates.Intrinsic.sourceMap p k n u ≫
      (MorphismCoverCoordinates.sourceIso p k n u).hom =
    (GC).map (MorphismSourceRefinementCoordinates.map p k n u) := by
  have h := RefinedCoefficientCoordinateSquare.square GC
    (ordinaryMap p k n u) (𝟙 _)
    (MorphismCoverCoordinates.sourceBaseIso p k n u)
    (Small.OrdinaryCechTotal.Ordinary.totalIso R X₁) (MorphismSourceRefinementCoordinates.map p k n u)
    (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G (NonemptyCechNerve.nerve V)
      (Small.OrdinaryCechTotal.Ordinary.finiteIndices R X₁) D)
    (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G (NonemptyCechNerve.nerve U)
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) ((F).op ⋙ D))
    (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G (NonemptyCechNerve.nerve U)
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) ((F).op ⋙ D))
    (MorphismOrdinaryCech.Ordinary.sourceOrdinaryRefinement p k n u) (𝟙 _)
    (GeometricComparison.CechAssembly.RefinedCoefficient.CechAssemblyRefinedCoefficient.total F G U V r D)
    (by
      erw [(GC).map_id]
      simp only [Category.id_comp, Category.comp_id])
    (by simpa only [Category.id_comp] using ordinary_coordinates p k n u)
  simpa only [MorphismIntrinsicCoordinates.Intrinsic.sourceMap,
    OrdinaryCechCoordinates.Ordinary.iso,
    MorphismCoverCoordinates.sourceIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.id_comp, Category.assoc] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementCoordinates
