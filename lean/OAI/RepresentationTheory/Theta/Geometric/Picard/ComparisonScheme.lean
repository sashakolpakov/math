import OAI.RepresentationTheory.Theta.Geometric.RigidifiedPicardDifference
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ZeroSchemeFiniteType

/-! # Comparison Scheme -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.ComparisonScheme

noncomputable section

/-! The equality locus of two rigidified Picard families is an actual
scheme of finite type over the parameter space, on all test schemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    {A B : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    [IsLocallyNoetherian B.left] (D F : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B)

def picardComparisonScheme : Over B.left := (RigidifiedPicardDifference.rigidifiedPicardDifference D F).zeroScheme

instance picardComparisonScheme_mono : Mono (picardComparisonScheme D F).hom :=
  inferInstanceAs (Mono (RigidifiedPicardDifference.rigidifiedPicardDifference D F).zeroScheme.hom)

instance picardComparisonScheme_locallyOfFiniteType :
    LocallyOfFiniteType (picardComparisonScheme D F).hom :=
  inferInstanceAs (LocallyOfFiniteType (RigidifiedPicardDifference.rigidifiedPicardDifference D F).zeroScheme.hom)

instance picardComparisonScheme_quasiCompact : QuasiCompact (picardComparisonScheme D F).hom :=
  inferInstanceAs (QuasiCompact (RigidifiedPicardDifference.rigidifiedPicardDifference D F).zeroScheme.hom)

theorem picardComparisonScheme_hasLift_iff {T : Over (Spec (.of K))} (a : T ⟶ B) :
    Nonempty (Over.mk a.left ⟶ picardComparisonScheme D F) ↔ D.relativeValue a = F.relativeValue a :=
  ((RigidifiedPicardDifference.rigidifiedPicardDifference D F).zeroScheme_hasLift_iff a).trans
    (RigidifiedPicardDifference.rigidifiedPicardDifference_zero_iff D F a)

def picardComparisonOver : Over (Spec (.of K)) :=
  (RigidifiedPicardDifference.rigidifiedPicardDifference D F).zeroSchemeOver

def picardComparisonInclusion : picardComparisonOver D F ⟶ B :=
  (RigidifiedPicardDifference.rigidifiedPicardDifference D F).zeroInclusion

instance picardComparisonInclusion_mono : Mono (picardComparisonInclusion D F) :=
  inferInstanceAs (Mono (RigidifiedPicardDifference.rigidifiedPicardDifference D F).zeroInclusion)

instance picardComparisonInclusion_left_locallyOfFiniteType :
    LocallyOfFiniteType (picardComparisonInclusion D F).left :=
  inferInstanceAs (LocallyOfFiniteType (RigidifiedPicardDifference.rigidifiedPicardDifference D F).zeroScheme.hom)

instance picardComparisonInclusion_left_quasiCompact :
    QuasiCompact (picardComparisonInclusion D F).left :=
  inferInstanceAs (QuasiCompact (RigidifiedPicardDifference.rigidifiedPicardDifference D F).zeroScheme.hom)

theorem picardComparison_factorization {T : Over (Spec (.of K))} (a : T ⟶ B) :
    D.relativeValue a = F.relativeValue a ↔
      ∃ z : T ⟶ picardComparisonOver D F, z ≫ picardComparisonInclusion D F = a :=
  (RigidifiedPicardDifference.rigidifiedPicardDifference_zero_iff D F a).symm.trans
    ((RigidifiedPicardDifference.rigidifiedPicardDifference D F).zeroInclusion_factorization T a)

theorem picardComparison_compares {T : Over (Spec (.of K))}
    (z : T ⟶ picardComparisonOver D F) :
    D.relativeValue (z ≫ picardComparisonInclusion D F) =
      F.relativeValue (z ≫ picardComparisonInclusion D F) :=
  (picardComparison_factorization D F _).mpr ⟨z, rfl⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.ComparisonScheme
