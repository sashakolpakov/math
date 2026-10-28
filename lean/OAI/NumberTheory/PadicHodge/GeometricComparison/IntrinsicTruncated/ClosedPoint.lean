import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.EtaleLift
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.Identity

/-! # Closed Point -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

section

/-! The original abelian identity point lifts uniquely to the genuine
finite etale source over the identity of the truncated target. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.specialIdentitySection_shift (m : ℕ) :
    A.specialIdentitySection ≫ A.truncatedShiftSpecial m = A.specialIdentitySection :=
  congrArg Over.Hom.left (MonObj.one_comp
    ((m : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
      OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom
    (X := Over.mk (𝟙 (Spec (.of (ZMod q))))))

theorem Geometry.AbelianH1Model.existsUnique_truncatedShiftIdentitySection (n m : ℕ) (hm : ¬q ∣ m) :
    ∃! s : Spec (.of (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)) ⟶ A.truncatedShiftSource n m hm,
      Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)) ≫ s =
        A.specialIdentitySection ≫ A.truncatedShiftReduction n m hm ∧
      s ≫ A.truncatedShiftMap n m hm = A.truncatedIdentitySection n := by
  let : IsFinite (A.truncatedShiftSpecial m) := (A.nativeFrobeniusShift_finite_etale m hm).1
  let : AlgebraicGeometry.Etale (A.truncatedShiftSpecial m) :=
    (A.nativeFrobeniusShift_finite_etale m hm).2.2
  apply IntegralComparison.Etale.SourcePointLift.existsUnique_point_lift (A.truncatedReduction n)
    (A.truncatedReduction_ker_nilpotent n) (A.truncatedShiftSpecial m)
    (Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)))
    (IntrinsicTruncated.Identity.NativeTruncatedBase.reduction_ker_nilpotent q n)
    A.specialIdentitySection (A.truncatedIdentitySection n)
  rw [← Category.assoc, A.specialIdentitySection_shift, A.truncatedIdentitySection_reduction]

def Geometry.AbelianH1Model.truncatedShiftIdentitySection (n m : ℕ) (hm : ¬q ∣ m) :
    Spec (.of (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)) ⟶ A.truncatedShiftSource n m hm :=
  (A.existsUnique_truncatedShiftIdentitySection n m hm).choose

@[reassoc] theorem Geometry.AbelianH1Model.truncatedShiftIdentitySection_reduction (n m : ℕ) (hm : ¬q ∣ m) :
    Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)) ≫
      A.truncatedShiftIdentitySection n m hm =
        A.specialIdentitySection ≫ A.truncatedShiftReduction n m hm :=
  (A.existsUnique_truncatedShiftIdentitySection n m hm).choose_spec.1.1

@[reassoc] theorem Geometry.AbelianH1Model.truncatedShiftIdentitySection_map (n m : ℕ) (hm : ¬q ∣ m) :
    A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm = A.truncatedIdentitySection n :=
  (A.existsUnique_truncatedShiftIdentitySection n m hm).choose_spec.1.2

theorem Geometry.AbelianH1Model.truncatedShiftIdentitySection_over (n m : ℕ) (hm : ¬q ∣ m) :
    A.truncatedShiftIdentitySection n m hm ≫ (A.truncatedShiftModel n m hm).hom = 𝟙 _ := by
  change A.truncatedShiftIdentitySection n m hm ≫
    A.truncatedShiftMap n m hm ≫ (A.truncatedModel n).scheme.hom = 𝟙 _
  rw [← Category.assoc, A.truncatedShiftIdentitySection_map, A.truncatedIdentitySection_over]

end

/-! The actual identity sections are closed immersions over the
one-point finite-level and residue bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

instance Geometry.AbelianH1Model.truncatedIdentitySection_closed (n : ℕ) : IsClosedImmersion (A.truncatedIdentitySection n) := by
  let : Subsingleton (Spec (CommRingCat.of (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n))) :=
    Ring.KrullDimLE.subsingleton_primeSpectrum (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
  exact isClosedImmersion_of_comp_eq_id (A.truncatedModel n).scheme.hom
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)

instance Geometry.AbelianH1Model.truncatedShiftIdentitySection_closed (n m : ℕ) (hm : ¬q ∣ m) :
    IsClosedImmersion (A.truncatedShiftIdentitySection n m hm) := by
  let : Subsingleton (Spec (CommRingCat.of (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n))) :=
    Ring.KrullDimLE.subsingleton_primeSpectrum (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
  exact isClosedImmersion_of_comp_eq_id (A.truncatedShiftModel n m hm).hom
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)

instance Geometry.AbelianH1Model.specialIdentitySection_closed : IsClosedImmersion A.specialIdentitySection := by
  let : Subsingleton (Spec (CommRingCat.of (ZMod q))) :=
    Ring.KrullDimLE.subsingleton_primeSpectrum (ZMod q)
  exact isClosedImmersion_of_comp_eq_id A.specialFiber.scheme.hom A.specialIdentitySection
    A.specialIdentitySection_over

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
