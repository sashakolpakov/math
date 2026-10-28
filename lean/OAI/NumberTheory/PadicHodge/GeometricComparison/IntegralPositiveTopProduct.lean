import OAI.NumberTheory.PadicHodge.GeometricComparison.FieldPositiveTopProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeIsoPositiveProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CoverPositiveProduct

/-! # Integral Positive Top Product -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

section

/-! The original generic-fiber isomorphism carries the number-field
top product to the inverse image of the integral model's affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

abbrev Geometry.AbelianH1Model.localPositiveVariety := (A.variety.pullback (Geometry.scalarBaseMap jq)).scheme

def Geometry.AbelianH1Model.localPositiveProjection : A.localPositiveVariety.left ⟶ A.variety.scheme.left :=
  pullback.fst A.variety.scheme.hom (Geometry.scalarBaseMap jq)

theorem Geometry.AbelianH1Model.localPositiveSquare :
    IsPullback A.localPositiveProjection A.localPositiveVariety.hom
      A.variety.scheme.hom (Spec.map (CommRingCat.ofHom jq)) :=
  IsPullback.of_hasPullback _ _

def Geometry.AbelianH1Model.localPositiveVarietyCover :
    Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index K A.variety.scheme → A.localPositiveVariety.left.Opens :=
  fun i => A.localPositiveProjection ⁻¹ᵁ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens K A.variety.scheme i

theorem Geometry.AbelianH1Model.localPositiveVarietyCover_covers : iSup A.localPositiveVarietyCover = ⊤ :=
  Affine.BaseChangeCover.AffineBaseChangeCover.cover A.variety.scheme A.localPositiveVariety
    A.localPositiveProjection _ (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover K A.variety.scheme)

theorem Geometry.AbelianH1Model.localPositiveVarietyCover_affine (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index K A.variety.scheme) :
    IsAffineOpen (A.localPositiveVarietyCover i) :=
  Affine.BaseChangeCover.AffineBaseChangeCover.affine jq A.variety.scheme A.localPositiveVariety
    A.localPositiveProjection A.localPositiveSquare _
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine K A.variety.scheme i)

abbrev Geometry.AbelianH1Model.localPositiveVarietyH (n : ℕ) :=
  (IntegralComparison.IntegralDeRham.CechProduct.total ℚ_[q] A.localPositiveVariety
    (IntegralComparison.NonemptyCechNerve.nerve A.localPositiveVarietyCover)).homology n

abbrev Geometry.AbelianH1Model.localPositiveVarietyCup (i j : ℕ)
    (x : A.localPositiveVarietyH i) (y : A.localPositiveVarietyH j) :=
  IntegralComparison.IntegralDeRham.CechProduct.cohomologyCup ℚ_[q] A.localPositiveVariety
    (IntegralComparison.NonemptyCechNerve.nerve A.localPositiveVarietyCover) i j x y

theorem Geometry.AbelianH1Model.localPositiveVarietyTopProduct (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (n : ℕ) (hn : n+1 = 2*A.dimension) :
    ∃ v : Fin (n+1) → A.localPositiveVarietyH 1,
      IntegralComparison.GradedPositiveProduct.product A.localPositiveVarietyCup n v ≠ 0 := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap K ℚ_[q] A.variety.scheme
      A.localPositiveVariety A.localPositiveProjection A.localPositiveSquare.w
      (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens K A.variety.scheme) (n+1)) :=
    IntegralComparison.Integral.CoverScalarIso.homologyMap_isIso K ℚ_[q] A.variety.scheme
      A.localPositiveVariety A.localPositiveProjection A.localPositiveSquare (n+1)
  exact IntegralComparison.Intrinsic.ScalarPositiveProduct.target_exists_nonzero K ℚ_[q] A.variety.scheme
    A.localPositiveVariety A.localPositiveProjection A.localPositiveSquare.w
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens K A.variety.scheme) n (A.numberFieldPositiveTopProduct j P n hn)

def Geometry.AbelianH1Model.integralPositiveProjection : A.localFiber.scheme.left ⟶ A.integral.scheme.left :=
  pullback.fst A.integral.scheme.hom (Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))

theorem Geometry.AbelianH1Model.integralPositiveSquare :
    IsPullback A.integralPositiveProjection A.localFiber.scheme.hom A.integral.scheme.hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[q] ℚ_[q]))) :=
  IsPullback.of_hasPullback _ _

def Geometry.AbelianH1Model.localPositiveCover :
    Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[q] A.integral.scheme → A.localFiber.scheme.left.Opens :=
  fun i => A.integralPositiveProjection ⁻¹ᵁ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[q] A.integral.scheme i

theorem Geometry.AbelianH1Model.localPositiveCover_covers : iSup A.localPositiveCover = ⊤ :=
  Affine.BaseChangeCover.AffineBaseChangeCover.cover A.integral.scheme A.localFiber.scheme
    A.integralPositiveProjection _ (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[q] A.integral.scheme)

theorem Geometry.AbelianH1Model.localPositiveCover_affine (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[q] A.integral.scheme) :
    IsAffineOpen (A.localPositiveCover i) :=
  Affine.BaseChangeCover.AffineBaseChangeCover.affine (algebraMap ℤ_[q] ℚ_[q]) A.integral.scheme A.localFiber.scheme
    A.integralPositiveProjection A.integralPositiveSquare _
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[q] A.integral.scheme i)

abbrev Geometry.AbelianH1Model.localPositiveH (n : ℕ) :=
  (IntegralComparison.IntegralDeRham.CechProduct.total ℚ_[q] A.localFiber.scheme
    (IntegralComparison.NonemptyCechNerve.nerve A.localPositiveCover)).homology n

abbrev Geometry.AbelianH1Model.localPositiveCup (i j : ℕ) (x : A.localPositiveH i) (y : A.localPositiveH j) :=
  IntegralComparison.IntegralDeRham.CechProduct.cohomologyCup ℚ_[q] A.localFiber.scheme
    (IntegralComparison.NonemptyCechNerve.nerve A.localPositiveCover) i j x y

theorem Geometry.AbelianH1Model.localPositiveTopProduct (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (n : ℕ) (hn : n+1 = 2*A.dimension) :
    ∃ v : Fin (n+1) → A.localPositiveH 1,
      IntegralComparison.GradedPositiveProduct.product A.localPositiveCup n v ≠ 0 := by
  let : A.localFiber.scheme.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.localFiber.scheme.hom]
    infer_instance
  let V := IntegralComparison.SchemeIsoPositiveProduct.inverseCover ℚ_[q] A.localPositiveVariety
    A.localFiber.scheme A.genericIso A.localPositiveVarietyCover
  have hV : iSup V = ⊤ := IntegralComparison.SchemeIsoPositiveProduct.cover ℚ_[q] A.localPositiveVariety
    A.localFiber.scheme A.genericIso A.localPositiveVarietyCover A.localPositiveVarietyCover_covers
  have haV : ∀ i, IsAffineOpen (V i) := IntegralComparison.SchemeIsoPositiveProduct.affine ℚ_[q] A.localPositiveVariety
    A.localFiber.scheme A.genericIso A.localPositiveVarietyCover A.localPositiveVarietyCover_affine
  have htop := IntegralComparison.SchemeIsoPositiveProduct.exists_nonzero ℚ_[q] A.localPositiveVariety
    A.localFiber.scheme A.genericIso A.localPositiveVarietyCover A.localPositiveVarietyCover_affine n
    (A.localPositiveVarietyTopProduct j P n hn)
  exact IntegralComparison.Rational.CoverPositiveProduct.exists_nonzero ℚ_[q] A.localFiber.scheme V A.localPositiveCover
    hV A.localPositiveCover_covers haV A.localPositiveCover_affine n htop

end

/-! Genuine integral degree-one classes have a top cup product whose
image in the actual rational generic-fiber cohomology is nonzero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

abbrev Geometry.AbelianH1Model.integralPositiveH (n : ℕ) :=
  (IntegralComparison.IntegralDeRham.CechProduct.total ℤ_[q] A.integral.scheme
    (IntegralComparison.NonemptyCechNerve.nerve (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[q] A.integral.scheme))).homology n

abbrev Geometry.AbelianH1Model.integralPositiveCup (i j : ℕ) (x : A.integralPositiveH i) (y : A.integralPositiveH j) :=
  IntegralComparison.IntegralDeRham.CechProduct.cohomologyCup ℤ_[q] A.integral.scheme
    (IntegralComparison.NonemptyCechNerve.nerve (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[q] A.integral.scheme)) i j x y

abbrev Geometry.AbelianH1Model.integralPositiveScalarMap (n : ℕ) : A.integralPositiveH n →+ A.localPositiveH n :=
  IntegralComparison.Intrinsic.ScalarPositiveProduct.map ℤ_[q] ℚ_[q] A.integral.scheme A.localFiber.scheme
    A.integralPositiveProjection A.integralPositiveSquare.w
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[q] A.integral.scheme) n

theorem Geometry.AbelianH1Model.integralPositiveTopProduct (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (n : ℕ) (hn : n+1 = 2*A.dimension) :
    ∃ v : Fin (n+1) → A.integralPositiveH 1,
      A.integralPositiveScalarMap (n+1)
        (IntegralComparison.GradedPositiveProduct.product A.integralPositiveCup n v) ≠ 0 := by
  let : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap ℤ_[q] ℚ_[q] A.integral.scheme
      A.localFiber.scheme A.integralPositiveProjection A.integralPositiveSquare.w
      (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[q] A.integral.scheme) 1) :=
    IntegralComparison.Integral.CoverScalarIso.homologyMap_isIso ℤ_[q] ℚ_[q] A.integral.scheme
      A.localFiber.scheme A.integralPositiveProjection A.integralPositiveSquare 1
  exact IntegralComparison.Intrinsic.ScalarPositiveProduct.image_exists_nonzero ℤ_[q] ℚ_[q] A.integral.scheme
    A.localFiber.scheme A.integralPositiveProjection A.integralPositiveSquare.w
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[q] A.integral.scheme) n (A.localPositiveTopProduct j P n hn)

theorem Geometry.AbelianH1Model.integralPositiveScalarMap_apply (n : ℕ) (x : A.integralPositiveH n) :
    A.integralPositiveScalarMap n x =
      (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap ℤ_[q] ℚ_[q] A.integral.scheme
        A.localFiber.scheme A.integralPositiveProjection A.integralPositiveSquare.w
        (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[q] A.integral.scheme) n).hom (1 ⊗ₜ[ℤ_[q]] x) := by
  unfold Geometry.AbelianH1Model.integralPositiveScalarMap IntegralComparison.Intrinsic.ScalarPositiveProduct.map
  rw [IntegralComparison.IntrinsicDeRham.CechScalarCoordinates.Intrinsic.homologyMap]
  rfl

theorem Geometry.AbelianH1Model.integralPositiveTopProduct_tensor (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (n : ℕ) (hn : n+1 = 2*A.dimension) :
    ∃ v : Fin (n+1) → A.integralPositiveH 1,
      (1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] (IntegralComparison.GradedPositiveProduct.product A.integralPositiveCup n v) ≠ 0 := by
  obtain ⟨v, hv⟩ := A.integralPositiveTopProduct j P n hn
  refine ⟨v, ?_⟩
  intro hz
  apply hv
  rw [A.integralPositiveScalarMap_apply, hz, map_zero]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
