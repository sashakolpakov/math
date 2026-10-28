import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.RegularSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenRegularDifference
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Refinement
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.PairPullback

/-! # Pulled Pair Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.PulledPairRefinement

noncomputable section

/-! On a compatible affine source cover, the refined pullback of
the original target tangent pair is its literal section pullback on
each original affine overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Family.AffineCoverIntersections.familyCoverAffineOpen Family.AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] Fixed.CechCover.fixedFamilyCechCover TangentBasePoint.fixedFamilyFiber FixedFiber.CoordinateProjection.fixedFiberAffineOpen
attribute [local implicit_reducible] FixedFiber.AffineDiagram.fixedFiberTensorAlgebras Affine.OpenDiagram.familyAffineCoordinateFunctor
attribute [local implicit_reducible] HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor
attribute [local irreducible] FixedFiber.RegularSections.fixedFiberRegularSectionEquiv FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference

variable (R : Type) [CommRing R] [Algebra R ℂ] {X Y : Over (Spec (.of R))}
    (f : X ⟶ Y) (D : X.left.AffineOpenCover) (V : Y.left.AffineOpenCover)
    (s : D.I₀ → V.I₀)
    (hs : ∀ i, (Family.AffineCoverIntersections.familyCoverAffineOpen R X D i).1 ≤ f.left ⁻¹ᵁ (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s i)).1)

include hs

theorem familyMorphismFixedCechRefinement (i : D.I₀) :
    Fixed.CechCover.fixedFamilyCechCover ℂ R X D i ≤
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f).left ⁻¹ᵁ Fixed.CechCover.fixedFamilyCechCover ℂ R Y V (s i) :=
  FamilyMorphism.RegularSections.familyMorphismFixedFiber_open_le R ℂ f (Family.AffineCoverIntersections.familyCoverAffineOpen R X D i) (Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s i)) (hs i)

variable [IsSeparated X.hom] [IsSeparated Y.hom]

omit [Algebra R ℂ] in
theorem familyMorphismCoverPair_image (i j : D.I₀) :
    (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X D i j).1 ≤ f.left ⁻¹ᵁ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R Y V (s i) (s j)).1 :=
  fun _ h => ⟨hs i h.1, hs j h.2⟩

variable [Algebra ℂ R] [IsScalarTower ℂ R ℂ] [Smooth Y.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R Y).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R Y).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R Y)]

def familyTangentPulledRefinedPair (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    ∀ i j : D.I₀, Γ((TangentBasePoint.fixedFamilyFiber ℂ R X).left, Fixed.CechCover.fixedFamilyCechCover ℂ R X D i ⊓ Fixed.CechCover.fixedFamilyCechCover ℂ R X D j) :=
  RegularPair.Refinement.regularPairRefinement (TangentBasePoint.fixedFamilyFiber ℂ R X).left
    (fun i => ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f).left ⁻¹ᵁ Fixed.CechCover.fixedFamilyCechCover ℂ R Y V i)
    (Fixed.CechCover.fixedFamilyCechCover ℂ R X D) s (familyMorphismFixedCechRefinement R f D V s hs)
    (RegularPair.PairPullback.regularPairPullback ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f).left
      (Fixed.CechCover.fixedFamilyCechCover ℂ R Y V) (RegularCocycle.familyTangentRegularPair R Y V d z))

omit [IsSeparated X.hom] in
theorem familyTangentPulledRefinedPair_cocycle (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    RegularPair.Closed.RegularPairCocycle (TangentBasePoint.fixedFamilyFiber ℂ R X).left (Fixed.CechCover.fixedFamilyCechCover ℂ R X D)
      (familyTangentPulledRefinedPair R f D V s hs d z) :=
  RegularPair.Refinement.regularPairRefinement_cocycle (TangentBasePoint.fixedFamilyFiber ℂ R X).left _ _ _ _ _
    (RegularPair.PairPullback.regularPairPullback_cocycle ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f).left
      (Fixed.CechCover.fixedFamilyCechCover ℂ R Y V) (RegularCocycle.familyTangentRegularPair R Y V d z) (RegularCocycle.familyTangentRegularPair_cocycle R Y V d z))

theorem familyTangentPulledRefinedPair_apply (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) (i j : D.I₀) :
    familyTangentPulledRefinedPair R f D V s hs d z i j =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f).left.appLE
        (FixedFiber.CoordinateProjection.fixedFiberAffineOpen R ℂ Y (Family.AffineCoverIntersections.familyCoverPairAffineOpen R Y V (s i) (s j)))
        (FixedFiber.CoordinateProjection.fixedFiberAffineOpen R ℂ X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X D i j))
        (FamilyMorphism.RegularSections.familyMorphismFixedFiber_open_le R ℂ f (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X D i j)
          (Family.AffineCoverIntersections.familyCoverPairAffineOpen R Y V (s i) (s j)) (familyMorphismCoverPair_image R f D V s hs i j))
        (Family.CommonOpenRegularDifference.familyCommonOpenRegularDifference R Y (V := Family.AffineCoverIntersections.familyCoverPairAffineOpen R Y V (s i) (s j))
          (W := Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s i)) (Z := Family.AffineCoverIntersections.familyCoverAffineOpen R Y V (s j))
          inf_le_left inf_le_right d z) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.PulledPairRefinement
