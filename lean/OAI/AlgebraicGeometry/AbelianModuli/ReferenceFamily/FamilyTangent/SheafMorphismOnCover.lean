import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.CoverCoboundary
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassDifference
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction

/-! # Sheaf Morphism On Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.SheafMorphismOnCover

noncomputable section

/-! The actual regular defect coboundary on a compatible affine
cover identifies the original source tangent sheaf class with the
native pullback of the original target tangent sheaf class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] TangentBasePoint.fixedFamilyFiber

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
    (D U : Scheme.AffineOpenCover.{0, 0} X.left) (V : Scheme.AffineOpenCover.{0, 0} Y.left)
    (r : D.I₀ → U.I₀) (s : D.I₀ → V.I₀)
    (hr : ∀ i, (Family.AffineCoverIntersections.familyCoverAffineOpen R X D i).1 ≤ (Family.AffineCoverIntersections.familyCoverAffineOpen R X U (r i)).1)
    (hs : ∀ i, (Family.AffineCoverIntersections.familyCoverAffineOpen R X D i).1 ≤ f.left ⁻¹ᵁ (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s i)).1)

include hr hs

theorem familyTangentSheafClass_morphism_onCover (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    Family.BaseTangentObstruction.familyTangentSheafClass R X U d
        (Intrinsic.GroupConormalMap.constructedConormalPullback (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f) z) =
      StructurePullbackLinear.nativeStructureH1PullbackLinear (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f)
        (Family.BaseTangentObstruction.familyTangentSheafClass R Y V d z) := by
  let F : TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f
  let p := FamilyMorphism.CoverCoboundary.familyTangentRefinedSourcePair R f D U r hr d z
  let w := PulledPairRefinement.familyTangentPulledRefinedPair R f D V s hs d z
  have hp := FamilyMorphism.CoverCoboundary.familyTangentRefinedSourcePair_cocycle R f D U r hr d z
  have hw := PulledPairRefinement.familyTangentPulledRefinedPair_cocycle R f D V s hs d z
  have hc := RegularPair.ClassDifference.regularPairSheafClass_eq_of_localDefects (TangentBasePoint.fixedFamilyFiber ℂ R X).left
    (Fixed.CechCover.fixedFamilyCechCover ℂ R X D) p w (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X D) hp hw
    (FamilyMorphism.CoverCoboundary.familyMorphismCoverDefect R f D U V r s hr hs d z)
    (FamilyMorphism.CoverCoboundary.familyMorphismCoverDefect_boundary R f D U V r s hr hs d z)
  have hsource := RegularPair.Refinement.regularPairSheafClass_refinement (TangentBasePoint.fixedFamilyFiber ℂ R X).left
    (Fixed.CechCover.fixedFamilyCechCover ℂ R X U) (Fixed.CechCover.fixedFamilyCechCover ℂ R X D) r (RegularPairRefinement.fixedFamilyCechCover_refinement R X U D r hr)
    (RegularCocycle.familyTangentRegularPair R X U d (Intrinsic.GroupConormalMap.constructedConormalPullback F z))
    (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X U) (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X D)
    (RegularCocycle.familyTangentRegularPair_cocycle R X U d (Intrinsic.GroupConormalMap.constructedConormalPullback F z))
  have htarget := RegularPair.Refinement.regularPairSheafClass_refinement (TangentBasePoint.fixedFamilyFiber ℂ R X).left
    (fun i => F.left ⁻¹ᵁ Fixed.CechCover.fixedFamilyCechCover ℂ R Y V i) (Fixed.CechCover.fixedFamilyCechCover ℂ R X D)
    s (PulledPairRefinement.familyMorphismFixedCechRefinement R f D V s hs)
    (RegularPair.PairPullback.regularPairPullback F.left (Fixed.CechCover.fixedFamilyCechCover ℂ R Y V) (RegularCocycle.familyTangentRegularPair R Y V d z))
    (Inverse.ImageCechCover.inverseImageCechCover_covers F.left.base (Fixed.CechCover.fixedFamilyCechCover ℂ R Y V) (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R Y V))
    (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R X D)
    (RegularPair.PairPullback.regularPairPullback_cocycle F.left (Fixed.CechCover.fixedFamilyCechCover ℂ R Y V)
      (RegularCocycle.familyTangentRegularPair R Y V d z) (RegularCocycle.familyTangentRegularPair_cocycle R Y V d z))
  have hq := RegularPair.ClassPullback.regularPairSheafClass_pullbackLinear F (Fixed.CechCover.fixedFamilyCechCover ℂ R Y V)
    (Fixed.CechCover.fixedFamilyCechCover_covers ℂ R Y V) (RegularCocycle.familyTangentRegularPair R Y V d z) (RegularCocycle.familyTangentRegularPair_cocycle R Y V d z)
  exact hsource.symm.trans (hc.trans (htarget.trans hq.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.SheafMorphismOnCover
