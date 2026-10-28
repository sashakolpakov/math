import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.MorphismRegularFormula
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.RegularPairRefinement
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.PulledPairRefinement

/-! # Cover Coboundary -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.CoverCoboundary

noncomputable section

/-! On an actual compatible affine cover, the refined original
source and pulled target tangent pair cocycles differ by the literal
coboundary of the constructed regular morphism defects. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Family.AffineCoverIntersections.familyCoverAffineOpen Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] Fixed.CechCover.fixedFamilyCechCover TangentBasePoint.fixedFamilyFiber FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local irreducible] FixedFiber.RegularSections.fixedFiberRegularSectionEquiv FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    [IsSeparated X.hom] [IsSeparated Y.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R Y).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R Y).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R Y)]
    (f : X ⟶ Y)
    [IsMonHom (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f)]
    (D U : X.left.AffineOpenCover) (V : Y.left.AffineOpenCover)
    (r : D.I₀ → U.I₀) (s : D.I₀ → V.I₀)
    (hr : ∀ i, (Family.AffineCoverIntersections.familyCoverAffineOpen R X D i).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r i)).1)
    (hs : ∀ i, (Family.AffineCoverIntersections.familyCoverAffineOpen R X D i).1 ≤ f.left ⁻¹ᵁ (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s i)).1)

def familyMorphismCoverDefect (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) (i : D.I₀) :
    Γ((TangentBasePoint.fixedFamilyFiber ℂ R X).left, Fixed.CechCover.fixedFamilyCechCover ℂ R X D i) :=
  RegularDefects.familyMorphismRegularDefect R f (Family.AffineCoverIntersections.familyCoverAffineOpen R X D i) (Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r i))
    (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s i)) (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s i))
    (hs i) (hr i) (le_refl _) d z

def familyTangentRefinedSourcePair (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    ∀ i j : D.I₀, Γ((TangentBasePoint.fixedFamilyFiber ℂ R X).left, Fixed.CechCover.fixedFamilyCechCover ℂ R X D i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X D j) :=
  RegularPair.Refinement.regularPairRefinement (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X U)
    (Fixed.CechCover.fixedFamilyCechCover ℂ R X D) r (FamilyTangent.RegularPairRefinement.fixedFamilyCechCover_refinement R X U D r hr)
    (FamilyTangent.RegularCocycle.familyTangentRegularPair R X U d
      (Intrinsic.GroupConormalMap.constructedConormalPullback (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f) z))

omit [Smooth Y.hom] [IsSeparated Y.hom]
    [IsMonHom (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f)] in
theorem familyTangentRefinedSourcePair_cocycle (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    RegularPair.Closed.RegularPairCocycle (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X D)
      (familyTangentRefinedSourcePair R f D U r hr d z) :=
  RegularPair.Refinement.regularPairRefinement_cocycle (TangentBasePoint.fixedFamilyFiber ℂ R X).left _ _ _ _ _
    (FamilyTangent.RegularCocycle.familyTangentRegularPair_cocycle R X U d _)

theorem familyMorphismCoverDefect_boundary (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) (i j : D.I₀) :
    familyTangentRefinedSourcePair R f D U r hr d z i j - FamilyTangent.PulledPairRefinement.familyTangentPulledRefinedPair R f D V s hs d z i j =
      (TangentBasePoint.fixedFamilyFiber ℂ R X).left.presheaf.map (homOfLE
        (show Fixed.CechCover.fixedFamilyCechCover ℂ R X D i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X D j ≤ Fixed.CechCover.fixedFamilyCechCover ℂ R X D j from inf_le_right)).op
        (familyMorphismCoverDefect R f D U V r s hr hs d z j) -
      (TangentBasePoint.fixedFamilyFiber ℂ R X).left.presheaf.map (homOfLE
        (show Fixed.CechCover.fixedFamilyCechCover ℂ R X D i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X D j ≤ Fixed.CechCover.fixedFamilyCechCover ℂ R X D i from inf_le_left)).op
        (familyMorphismCoverDefect R f D U V r s hr hs d z i) := by
  let F : TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f
  let hpair := FamilyTangent.PulledPairRefinement.familyMorphismCoverPair_image R f D V s hs i j
  have H := FamilyTangent.MorphismRegularFormula.familyTangentMorphism_regularFormula R f
    (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X D i j) (Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r i)) (Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r j))
    (Family.AffineCoverIntersections.familyCoverPairAffineOpen R Y V (s i) (s j)) (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s i)) (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s j))
    hpair (inf_le_left.trans (hr i)) (inf_le_right.trans (hr j)) inf_le_left inf_le_right d z
  have Hs := FamilyTangent.RegularPairRefinement.familyTangentRegularPair_refinement R X U D r hr d (Intrinsic.GroupConormalMap.constructedConormalPullback F z) i j
  have Ht := FamilyTangent.PulledPairRefinement.familyTangentPulledRefinedPair_apply R f D V s hs d z i j
  have Hi := RegularDefects.familyMorphismRegularDefect_restrict R f
    (Family.AffineCoverIntersections.familyCoverAffineOpen R X D i) (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X D i j) (Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r i))
    (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s i)) (Family.AffineCoverIntersections.familyCoverPairAffineOpen R Y V (s i) (s j)) (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s i))
    inf_le_left inf_le_left (hs i) hpair (hr i) (le_refl _) d z
  have Hj := RegularDefects.familyMorphismRegularDefect_restrict R f
    (Family.AffineCoverIntersections.familyCoverAffineOpen R X D j) (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X D i j) (Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r j))
    (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s j)) (Family.AffineCoverIntersections.familyCoverPairAffineOpen R Y V (s i) (s j)) (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s j))
    inf_le_right inf_le_right (hs j) hpair (hr j) (le_refl _) d z
  rw [← Hs, ← Ht, Hi, Hj] at H
  exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.CoverCoboundary
