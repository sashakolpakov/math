import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ResolvedNormalization
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SectionComplexPullback

/-! # Resolved Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ResolvedPullback.IntrinsicResolvedPullback

noncomputable section

/-! Actual geometric inverse image commutes with the native acyclic-resolution comparison whenever the actual resolution maps form a commuting square. -/

open _root_.CategoryTheory Limits Abelian _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _
local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) := HasDerivedCategory.standard _

def derivedMap {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℤ}
    {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℤ}
    (a : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).obj K ⟶ L) (n : ℤ)
    (x : (DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) 0).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :
    (DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) 0).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) ⟶ (DerivedCategory.Q.obj L)⟦n⟧ :=
  (DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) 0).map (DeRham.Int.inverseImageConstantIso f).inv ≫
    AcyclicExact.AcyclicExactFunctorNaturality.derivedMap (DeRham.Int.inverseImage f)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) a n x

theorem naturality
    {K K' : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℤ}
    {L L' : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℤ}
    (s : K ⟶ K') (t : L ⟶ L') [QuasiIso s] [QuasiIso t]
    (a : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (b : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
    (h : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).map s ≫ b = a ≫ t)
    (c d : ℤ) [K'.IsStrictlyGE c] [L'.IsStrictlyGE d]
    (hK : ∀ p q, Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) (K'.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) (L'.X p) (q + 1)))
    (n : ℤ) (x : (Section.Hypercohomology.SectionHypercohomology.sectionComplex R (TopCat.of Y.left) K').homology n) :
    ResolvedHypercohomologyEquiv.ResolvedHypercohomology.equiv R (TopCat.of X.left) t d hL n
      (HomologicalComplex.homologyMap (SectionComplexPullback.IntrinsicSectionComplexPullback.map f b) n x) =
      derivedMap f a n (ResolvedHypercohomologyEquiv.ResolvedHypercohomology.equiv R (TopCat.of Y.left) s c hK n x) := by
  let E := PackagedResolved.PackagedResolvedComparison.equivWithSystem R
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) (Section.Hypercohomology.SectionHypercohomology.comparisonSystem R (TopCat.of X.left)) t d hL n
  let z := Section.Hypercohomology.SectionHypercohomology.homologyEquiv R (TopCat.of Y.left) K' n x
  have h₁ := ResolvedNormalization.IntrinsicResolvedNormalization.equiv_apply R (TopCat.of X.left) t d hL n
    (HomologicalComplex.homologyMap (SectionComplexPullback.IntrinsicSectionComplexPullback.map f b) n x)
  have h₂ := congrArg E (SectionComplexPullback.IntrinsicSectionComplexPullback.homologyEquiv f b n x)
  have h₃ := PackagedResolved.PackagedResolvedComparison.with_coefficient_of_system_eq R (DeRham.Int.inverseImage f)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
    (DeRham.Int.inverseImageConstantIso f)
    (Section.Hypercohomology.SectionHypercohomology.comparisonSystem R (TopCat.of Y.left))
    (Section.Hypercohomology.SectionHypercohomology.comparisonSystem R (TopCat.of X.left)) rfl rfl
    s t a b h c d hK hL n z
  have h₄ := congrArg (derivedMap f a n)
    (ResolvedNormalization.IntrinsicResolvedNormalization.equiv_apply R (TopCat.of Y.left) s c hK n x).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ResolvedPullback.IntrinsicResolvedPullback
