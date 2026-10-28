import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ResolvedPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Composition

/-! # Resolved De Rham -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ResolvedDeRham.IntrinsicResolvedPullback

noncomputable section

/-! The geometric resolution map specializes to the original native de Rham pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _
local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) := HasExt.standard _

theorem derivedMap_deRham (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R Y n) :
    ResolvedPullback.IntrinsicResolvedPullback.derivedMap f (DeRham.Int.sheafPullbackInt f) (n : ℤ) x = DeRham.Int.pullback f n x := by
  have h := DerivedCoefficient.DerivedCoefficientTransport.map_eq_transport (DeRham.Int.inverseImage f)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
    (DeRham.Int.inverseImageConstantIso f) (DeRham.Int.sheafPullbackInt f) (n : ℤ) x
  exact h.trans (DeRham.Composition.pullback_transport f n x).symm

theorem deRham_naturality
    {K' : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ℤ}
    {L' : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℤ}
    (s : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y ⟶ K')
    (t : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X ⟶ L') [QuasiIso s] [QuasiIso t]
    (b : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
    (h : ((DeRham.Int.inverseImage f).mapHomologicalComplex (.up ℤ)).map s ≫ b =
      DeRham.Int.sheafPullbackInt f ≫ t)
    (c d : ℤ) [K'.IsStrictlyGE c] [L'.IsStrictlyGE d]
    (hK : ∀ p q, Subsingleton (Abelian.Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) (K'.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (Abelian.Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) (L'.X p) (q + 1)))
    (n : ℕ) (x : (Section.Hypercohomology.SectionHypercohomology.sectionComplex R (TopCat.of Y.left) K').homology (n : ℤ)) :
    ResolvedHypercohomologyEquiv.ResolvedHypercohomology.equiv R (TopCat.of X.left) t d hL (n : ℤ)
      (HomologicalComplex.homologyMap (SectionComplexPullback.IntrinsicSectionComplexPullback.map f b) (n : ℤ) x) =
      DeRham.Int.pullback f n (ResolvedHypercohomologyEquiv.ResolvedHypercohomology.equiv R (TopCat.of Y.left) s c hK (n : ℤ) x) :=
  (ResolvedPullback.IntrinsicResolvedPullback.naturality f s t (DeRham.Int.sheafPullbackInt f) b h c d hK hL (n : ℤ) x).trans
    (derivedMap_deRham f n _)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ResolvedDeRham.IntrinsicResolvedPullback
