import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.TruncatedModel
import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianField
import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentLineLifting
import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFiberProjectivity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.WittFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projectivity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.Padding
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PresentationGeometry

/-! # Projectivity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Projectivity of the original good-reduction model at every finite
Witt level, obtained by lifting a positive power of an actual ample
special-fiber line bundle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange

namespace IntrinsicTruncated.Projectivity.NativeTruncatedBase
variable (q : ℕ) [Fact q.Prime] (n : ℕ)
instance finite : Finite (TruncatedModel.NativeTruncatedBase.Ring q n) := IntegralComparison.Truncated.WittFinite.finite q (ZMod q) n
instance nontrivial : Nontrivial (TruncatedModel.NativeTruncatedBase.Ring q n) :=
  Function.Surjective.nontrivial (IntegralComparison.Truncated.Witt.reduction_surjective q (ZMod q) n)
instance localRing : IsLocalRing (TruncatedModel.NativeTruncatedBase.Ring q n) :=
  IsLocalRing.of_surjective' (IntegralComparison.Truncated.Witt.quotient q (ZMod q) n) Ideal.Quotient.mk_surjective
instance noetherianSections : IsNoetherianRing Γ(Spec (.of (TruncatedModel.NativeTruncatedBase.Ring q n)), ⊤) :=
  isNoetherianRing_of_ringEquiv (TruncatedModel.NativeTruncatedBase.Ring q n) (Scheme.ΓSpecIso (.of (TruncatedModel.NativeTruncatedBase.Ring q n))).commRingCatIsoToRingEquiv.symm
end IntrinsicTruncated.Projectivity.NativeTruncatedBase

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

instance Geometry.AbelianH1Model.truncatedModel_separated (n : ℕ) : (A.truncatedModel n).scheme.left.IsSeparated :=
  ⟨(terminal.comp_from (A.truncatedModel n).scheme.hom) ▸
    (inferInstance : IsSeparated ((A.truncatedModel n).scheme.hom ≫ terminal.from _))⟩

def Geometry.AbelianH1Model.specialFiberAmpleLine : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.specialFiber.scheme.left :=
  Classical.choose (AbelianField.AbelianFieldAmple.exists_ample A.specialFiber)

theorem Geometry.AbelianH1Model.specialFiberAmpleLine_isAmple : A.specialFiberAmpleLine.IsAmple :=
  Classical.choose_spec (AbelianField.AbelianFieldAmple.exists_ample A.specialFiber)

def Geometry.AbelianH1Model.truncatedAmpleLine (n : ℕ) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.truncatedModel n).scheme.left :=
  IntegralComparison.NilpotentLineLifting.lift q n (A.truncatedReduction n)
    (A.truncated_prime_power_zero n) (A.truncatedReduction_kernel n) A.specialFiberAmpleLine

def Geometry.AbelianH1Model.truncatedAmpleLineReductionIso (n : ℕ) :
    ((A.truncatedAmpleLine n).pullback (A.truncatedReduction n)).sheaf ≅
      (A.specialFiberAmpleLine.tensorPower (q ^ n)).sheaf :=
  IntegralComparison.NilpotentLineLifting.reductionIso q n (A.truncatedReduction n)
    (A.truncated_prime_power_zero n) (A.truncatedReduction_kernel n) A.specialFiberAmpleLine

theorem Geometry.AbelianH1Model.truncatedAmpleLine_reduction_isAmple (n : ℕ) :
    ((A.truncatedAmpleLine n).pullback (A.truncatedReduction n)).IsAmple :=
  ((A.specialFiberAmpleLine_isAmple).tensorPower (q ^ n)
    (Nat.pow_pos (Fact.out : q.Prime).pos)).of_iso (A.truncatedAmpleLineReductionIso n).symm

def Geometry.AbelianH1Model.truncatedProjectivePresentation (n : ℕ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (A.truncatedModel n).scheme :=
  IntegralComparison.NilpotentFiberProjectivity.Ampleness.projectivePresentation (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)
    (IntegralComparison.Truncated.Witt.reduction_surjective q (ZMod q) n)
    (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.kernel_nilpotent q n) (A.truncatedModel n).scheme.hom
    A.specialFiber.scheme.hom (A.truncatedReduction n) (A.truncatedReductionSquare n)
    (A.truncatedAmpleLine n) (A.truncatedAmpleLine_reduction_isAmple n)

theorem Geometry.AbelianH1Model.truncatedModel_projective (n : ℕ) :
    IntegralComparison.Projectivity.Construction.ProjectiveOver (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme.hom :=
  IntegralComparison.Projective.PresentationGeometry.projectiveOver _ _ (A.truncatedProjectivePresentation n)

/-- The ambient projective dimension is positive, as required by the
native projective residue trace. -/
theorem Geometry.AbelianH1Model.truncatedModel_projective_positive (n : ℕ) :
    ∃ (N : ℕ) (i : (A.truncatedModel n).scheme.left ⟶
      IntegralComparison.Projectivity.Construction.projectiveSpace (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (N + 1)),
      IsClosedImmersion i ∧
        i ≫ IntegralComparison.Projectivity.Construction.projectiveSpaceToSpec (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (N + 1) =
          (A.truncatedModel n).scheme.hom :=
  IntegralComparison.Projective.Padding.exists_positive _ _ (A.truncatedModel_projective n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
