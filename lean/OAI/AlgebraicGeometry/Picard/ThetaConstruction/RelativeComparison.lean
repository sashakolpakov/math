import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeRigidifiedOperations
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiniteType

/-! # Relative Comparison -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeComparison.Geometric

noncomputable section

/-! An actual scheme over the original base compares a parameterized
rigidified line with an arbitrary rigidified family. Its factorization
property is exactly equality in the original relative Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts

variable {S : Scheme} {A N T : Over S} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsLocallyNoetherian (N ⊗ T).left] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A)
    (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A N) (L : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A T)

def relativeComparisonLine : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A (N ⊗ T) :=
  RelativeRigidifiedOperations.Geometric.relativeRigidifiedQuotient (RelativeRigidifiedOperations.Geometric.relativeRigidifiedPullback D (fst N T))
    (RelativeRigidifiedOperations.Geometric.relativeRigidifiedPullback L (snd N T))

def relativePicardComparison : Over S := RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroSchemeOver (relativeComparisonLine D L) P

def relativePicardComparisonInclusion : relativePicardComparison P D L ⟶ N ⊗ T :=
  RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion (relativeComparisonLine D L) P

def relativePicardComparisonParameter : relativePicardComparison P D L ⟶ N :=
  relativePicardComparisonInclusion P D L ≫ fst N T

def relativePicardComparisonProjection : relativePicardComparison P D L ⟶ T :=
  relativePicardComparisonInclusion P D L ≫ snd N T

instance relativePicardComparisonInclusion_mono : Mono (relativePicardComparisonInclusion P D L) :=
  RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_mono P (relativeComparisonLine D L)

theorem relativePicardComparison_value {U : Over S}
    (z : U ⟶ relativePicardComparison P D L) :
    D.relativeValue (z ≫ relativePicardComparisonParameter P D L) =
      L.relativeValue (z ≫ relativePicardComparisonProjection P D L) := by
  have hz := (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion_factorization (relativeComparisonLine D L) P U
    (z ≫ relativePicardComparisonInclusion P D L)).mpr ⟨z, rfl⟩
  rw [relativeComparisonLine, RelativeRigidifiedOperations.Geometric.relativeRigidifiedQuotient_zero_iff, RelativeRigidifiedOperations.Geometric.relativeRigidifiedPullback_value,
    RelativeRigidifiedOperations.Geometric.relativeRigidifiedPullback_value] at hz
  exact (congrArg D.relativeValue (Category.assoc _ _ _).symm).trans
    (hz.trans (congrArg L.relativeValue (Category.assoc _ _ _)))

theorem relativePicardComparison_factorization {U : Over S} (a : U ⟶ N) (t : U ⟶ T) :
    D.relativeValue a = L.relativeValue t ↔
      ∃ z : U ⟶ relativePicardComparison P D L,
        z ≫ relativePicardComparisonParameter P D L = a ∧
          z ≫ relativePicardComparisonProjection P D L = t := by
  have h := RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion_factorization (relativeComparisonLine D L) P U (lift a t)
  rw [relativeComparisonLine, RelativeRigidifiedOperations.Geometric.relativeRigidifiedQuotient_zero_iff, RelativeRigidifiedOperations.Geometric.relativeRigidifiedPullback_value,
    RelativeRigidifiedOperations.Geometric.relativeRigidifiedPullback_value, lift_fst, lift_snd] at h
  constructor
  · intro he
    obtain ⟨z, hz⟩ := h.mp he
    refine ⟨z, ?_, ?_⟩
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ fst N T) hz).trans (lift_fst a t))
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ snd N T) hz).trans (lift_snd a t))
  · rintro ⟨z, ha, ht⟩
    have hv := relativePicardComparison_value P D L z
    rwa [ha, ht] at hv

theorem relativePicardComparisonProjection_mono
    (hD : ∀ U : Over S, Function.Injective (D.relativeValue (T := U))) :
    Mono (relativePicardComparisonProjection P D L) := by
  constructor
  intro U f g hfg
  apply (cancel_mono (relativePicardComparisonInclusion P D L)).mp
  apply CartesianMonoidalCategory.hom_ext
  · have hf := relativePicardComparison_value P D L f
    have hg := relativePicardComparison_value P D L g
    have he := hD U (hf.trans ((congrArg L.relativeValue hfg).trans hg.symm))
    exact (Category.assoc _ _ _).trans (he.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (hfg.trans (Category.assoc _ _ _).symm)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeComparison.Geometric
