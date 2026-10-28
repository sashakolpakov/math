import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinarySection
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.Iso
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex

/-! # Ordinary Cech Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechTotal.Ordinary

noncomputable section

/-! The ordinary complexes of the actual affine section rings compute
the native sheafified de Rham Čech total on the same small cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local notation "inclusion" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "NV" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve V

def diagram := (inclusion).op ⋙ GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly.diagram R X

def complexIso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (diagram R X) ≅
    ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u} R) inclusion).mapHomologicalComplex
      (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) :=
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.iso (inclusion).op (𝟭 (ModuleCat.{u} R)) (.up ℕ)
    (GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly.diagram R X)).symm ≪≫
      ((AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.transport (inclusion).op (𝟭 (ModuleCat.{u} R))).mapHomologicalComplex
        (.up ℕ)).mapIso (GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly.iso R X)

local instance tuple_preserves (m : ℕ) (t : Fin (m + 1) → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index R X) :
    PreservesLimit (Discrete.functor (U ∘ t)) inclusion :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.inclusion_preserves X.left (U ∘ t)

def bicomplexIso : GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex N
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (diagram R X)) ≅
      GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex NV (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) :=
  ((NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).mapIso (complexIso R X) ≪≫
    GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso inclusion U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def totalIso : GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total N (diagram R X) ≅ AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total R X :=
  HomologicalComplex₂.total.mapIso (bicomplexIso R X) (.up ℕ) ≪≫ AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.totalIso R X

theorem finiteIndices (m : SimplexCategory) : Finite ((N).obj (op m)).I := by
  change Finite (Fin (m.len + 1) → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index R X)
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechTotal.Ordinary
