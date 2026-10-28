import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ResolvedDeRham
import OAI.NumberTheory.PadicHodge.GeometricComparison.ShiftedInverse

/-! # Derived Map Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.DerivedMapSquare.IntrinsicResolvedPullback

noncomputable section

/-! Native geometric pullback commutes with arbitrary compatible cochain maps,
including the first-three projection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _
local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) := HasExt.standard _

theorem derivedMap_square
    {K K' : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℤ}
    {L L' : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℤ}
    (s : K ⟶ K') (t : L ⟶ L')
    (a : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (b : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
    (h : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).map s ≫ b = a ≫ t)
    (n : ℤ) (x : (DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) 0).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :
    ResolvedPullback.IntrinsicResolvedPullback.derivedMap f b n (x ≫ (DerivedCategory.Q.map s)⟦n⟧') =
      ResolvedPullback.IntrinsicResolvedPullback.derivedMap f a n x ≫ (DerivedCategory.Q.map t)⟦n⟧' := by
  let F := DeRham.Int.inverseImage f
  let A := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y
  let c := (DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) 0).map
    (DeRham.Int.inverseImageConstantIso f).inv
  have hs := ShiftedInverse.ShiftedMapSquare.naturality F.mapDerivedCategory
    ((F.mapDerivedCategorySingleFunctor 0).app A)
    (DerivedCategory.Q.map s) (DerivedCategory.Q.map t)
    (AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext.derivedComplexMap F a) (AlgebraicGeometry.Comparison.Betti.Derived.ResolutionNaturality.Ext.derivedComplexMap F b)
    (DerivedResolution.DerivedResolutionExactNaturality.square F s t a b h) n x
  have hb := DerivedResolution.DerivedResolutionExactNaturality.map_eq_transport F A b n
    (x ≫ (DerivedCategory.Q.map s)⟦n⟧')
  have ha := DerivedResolution.DerivedResolutionExactNaturality.map_eq_transport F A a n x
  have hh := hb.trans (hs.trans (congrArg (fun z => z ≫ (DerivedCategory.Q.map t)⟦n⟧') ha.symm))
  change c ≫ AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A b n (x ≫ (DerivedCategory.Q.map s)⟦n⟧') =
    (c ≫ AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A a n x) ≫ (DerivedCategory.Q.map t)⟦n⟧'
  exact (congrArg (fun z => c ≫ z) hh).trans (Category.assoc _ _ _).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.DerivedMapSquare.IntrinsicResolvedPullback
