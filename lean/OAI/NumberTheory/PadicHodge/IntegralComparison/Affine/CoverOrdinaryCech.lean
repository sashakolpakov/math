import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoverDeRhamUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechTotal

/-! # Cover Ordinary Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoverOrdinaryCech.Ordinary

noncomputable section

/-! Ordinary affine-ring de Rham coordinates for every affine
refinement of the smooth coordinate cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {ι : Type} (U : ι → X.left.affineOpens)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

local instance tuple_preserves (m : ℕ) (t : Fin (m + 1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t)) F :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.inclusion_preserves X.left (U ∘ t)

def bicomplexIso :
    GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex N
      (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (Small.OrdinaryCechTotal.Ordinary.diagram R X)) ≅
        CoverDeRhamUnit.bicomplex R X U :=
  ((NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).mapIso
      (Small.OrdinaryCechTotal.Ordinary.complexIso R X) ≪≫
    GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

variable (r : ι → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index R X)
  (hr : ∀ i, (U i).val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X (r i)).val)

def totalIso : GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total N (Small.OrdinaryCechTotal.Ordinary.diagram R X) ≅
    IntrinsicDeRham.CechComplex.Intrinsic.total R X (CoverDeRhamUnit.opens R X U) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso R X U) (.up ℕ) ≪≫
    CoverDeRhamUnit.totalIso R X U r hr

omit [IsProper X.hom] [Smooth X.hom] in
theorem finiteIndices [Finite ι] (m : SimplexCategory) : Finite ((N).obj (op m)).I := by
  change Finite (Fin (m.len + 1) → ι)
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoverOrdinaryCech.Ordinary
