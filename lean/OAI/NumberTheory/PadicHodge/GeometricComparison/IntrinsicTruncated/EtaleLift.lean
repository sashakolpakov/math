import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.Nilpotence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FrobeniusShiftDegree
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SourceLift

/-! # Etale Lift -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.EtaleLift

noncomputable section

/-! The actual finite etale lift of each prime-to-q shift [m]+F to
the original finite-level good-reduction target. Its source is the
scheme constructed by genuine etale chart gluing. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
namespace AbelianModel
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftSpecial (m : ℕ) : A.specialFiber.scheme.left ⟶ A.specialFiber.scheme.left :=
  ((m : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
    OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom.left

variable (n m : ℕ) (hm : ¬q ∣ m)

include hm in
private theorem shift_finite : IsFinite (A.truncatedShiftSpecial m) :=
  (A.nativeFrobeniusShift_finite_etale m hm).1
include hm in
private theorem shift_etale : AlgebraicGeometry.Etale (A.truncatedShiftSpecial m) :=
  (A.nativeFrobeniusShift_finite_etale m hm).2.2

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftSource : Scheme := by
  letI := (shift_finite A) m hm
  letI := (shift_etale A) m hm
  exact IntegralComparison.Etale.SourceLift.source (A.truncatedReduction n)
    (A.truncatedReduction_ker_nilpotent n) (A.truncatedShiftSpecial m)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftMap : A.truncatedShiftSource n m hm ⟶ (A.truncatedModel n).scheme.left := by
  letI := (shift_finite A) m hm
  letI := (shift_etale A) m hm
  exact IntegralComparison.Etale.SourceLift.map (A.truncatedReduction n)
    (A.truncatedReduction_ker_nilpotent n) (A.truncatedShiftSpecial m)

instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftMap_finite : IsFinite (A.truncatedShiftMap n m hm) := by
  let := (shift_finite A) m hm
  let := (shift_etale A) m hm
  exact IntegralComparison.FiniteEtale.SourceLift.map_finite (A.truncatedReduction n)
    (A.truncatedReduction_ker_nilpotent n) (A.truncatedShiftSpecial m)
instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftMap_etale : AlgebraicGeometry.Etale (A.truncatedShiftMap n m hm) := by
  let := (shift_finite A) m hm
  let := (shift_etale A) m hm
  exact IntegralComparison.Etale.SourceLift.map_etale (A.truncatedReduction n)
    (A.truncatedReduction_ker_nilpotent n) (A.truncatedShiftSpecial m)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftReduction : A.specialFiber.scheme.left ⟶ A.truncatedShiftSource n m hm := by
  letI := (shift_finite A) m hm
  letI := (shift_etale A) m hm
  exact IntegralComparison.Etale.SourceLift.reduction (A.truncatedReduction n)
    (A.truncatedReduction_ker_nilpotent n) (A.truncatedShiftSpecial m)

instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftReduction_closed : IsClosedImmersion (A.truncatedShiftReduction n m hm) := by
  let := (shift_finite A) m hm
  let := (shift_etale A) m hm
  exact IntegralComparison.Etale.SourceLift.reduction_closed (A.truncatedReduction n)
    (A.truncatedReduction_ker_nilpotent n) (A.truncatedShiftSpecial m)

instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftReduction_surjective : Surjective (A.truncatedShiftReduction n m hm) := by
  let := (shift_finite A) m hm
  let := (shift_etale A) m hm
  exact ⟨IntegralComparison.Etale.SourceLift.reduction_surjective (A.truncatedReduction n)
    (A.truncatedReduction_ker_nilpotent n) (A.truncatedShiftSpecial m)⟩

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftReduction_square :
    IsPullback (A.truncatedShiftReduction n m hm) (A.truncatedShiftSpecial m)
      (A.truncatedShiftMap n m hm) (A.truncatedReduction n) := by
  let := (shift_finite A) m hm
  let := (shift_etale A) m hm
  exact IntegralComparison.Etale.SourceLiftReduction.reduction_square (A.truncatedReduction n)
    (A.truncatedReduction_ker_nilpotent n) (A.truncatedShiftSpecial m)

@[reassoc] theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftReduction_map :
    A.truncatedShiftReduction n m hm ≫ A.truncatedShiftMap n m hm =
      A.truncatedShiftSpecial m ≫ A.truncatedReduction n :=
  (A.truncatedShiftReduction_square n m hm).w

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftModel : Over (Spec (.of (TruncatedModel.NativeTruncatedBase.Ring q n))) :=
  Over.mk (A.truncatedShiftMap n m hm ≫ (A.truncatedModel n).scheme.hom)

instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftModel_smooth : Smooth (A.truncatedShiftModel n m hm).hom :=
  inferInstanceAs (Smooth (A.truncatedShiftMap n m hm ≫ (A.truncatedModel n).scheme.hom))

instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftModel_proper : IsProper (A.truncatedShiftModel n m hm).hom :=
  inferInstanceAs (IsProper (A.truncatedShiftMap n m hm ≫ (A.truncatedModel n).scheme.hom))

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftModel_square :
    IsPullback (A.truncatedShiftReduction n m hm) A.specialFiber.scheme.hom
      (A.truncatedShiftModel n m hm).hom
      (Spec.map (CommRingCat.ofHom (TruncatedModel.NativeTruncatedBase.reduction q n))) := by
  have h := (A.truncatedShiftReduction_square n m hm).paste_vert (A.truncatedReductionSquare n)
  have hw : A.truncatedShiftSpecial m ≫ A.specialFiber.scheme.hom = A.specialFiber.scheme.hom :=
    ((m : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
      OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom.w
  rw [hw] at h
  exact h

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedShiftMap_finrank (x : A.specialFiber.scheme.left) :
    (A.truncatedShiftMap n m hm).finrank (A.truncatedReduction n x) =
      (A.truncatedShiftSpecial m).finrank x :=
  (Scheme.Hom.finrank_of_isPullback _ _ _ _ (A.truncatedShiftReduction_square n m hm) x).symm

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.nativeIntegerFrobeniusPolynomial_eval_neg_truncated_finrank
    (x : (A.truncatedModel n).scheme.left) :
    A.nativeIntegerFrobeniusPolynomial.eval (-(m : ℤ)) =
      ((A.truncatedShiftMap n m hm).finrank x : ℤ) := by
  obtain ⟨x₀, rfl⟩ := (A.truncatedReduction n).surjective x
  rw [A.truncatedShiftMap_finrank n m hm]
  exact A.nativeIntegerFrobeniusPolynomial_eval_neg_nat_finrank m hm x₀

end AbelianModel

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.EtaleLift
