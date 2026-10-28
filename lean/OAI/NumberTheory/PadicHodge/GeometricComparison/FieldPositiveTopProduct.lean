import OAI.NumberTheory.PadicHodge.GeometricComparison.BettiGroupAction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RelativeDimensionUnique
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.BaseChangeCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CoverScalarIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ScalarPositiveProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoverPositiveTopCup

/-! # Field Positive Top Product -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FieldPositiveTopProduct.AbelianModel

noncomputable section

/-! A nonzero top product on the complex fiber descends through the
actual scalar comparison to the original number-field affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.numberFieldPositiveH (n : ℕ) :=
  (IntegralComparison.IntegralDeRham.CechProduct.total K A.variety.scheme
    (IntegralComparison.NonemptyCechNerve.nerve (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens K A.variety.scheme))).homology n

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.numberFieldPositiveCup (i j : ℕ) (x : A.numberFieldPositiveH i) (y : A.numberFieldPositiveH j) :=
  IntegralComparison.IntegralDeRham.CechProduct.cohomologyCup K A.variety.scheme
    (IntegralComparison.NonemptyCechNerve.nerve (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens K A.variety.scheme)) i j x y

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.complexPositiveProjection (j : K →+* ℂ) :
    (A.complexFiber j).scheme.left ⟶ A.variety.scheme.left :=
  pullback.fst A.variety.scheme.hom (Geometry.scalarBaseMap j)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.complexPositiveSquare (j : K →+* ℂ) :
    IsPullback (A.complexPositiveProjection j) (A.complexFiber j).scheme.hom
      A.variety.scheme.hom (Spec.map (CommRingCat.ofHom j)) :=
  IsPullback.of_hasPullback _ _

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.complexPositiveCover (j : K →+* ℂ) :
    Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index K A.variety.scheme → (A.complexFiber j).scheme.left.Opens :=
  fun i => A.complexPositiveProjection j ⁻¹ᵁ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens K A.variety.scheme i

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.complexPositiveCover_covers (j : K →+* ℂ) : iSup (A.complexPositiveCover j) = ⊤ :=
  Affine.BaseChangeCover.AffineBaseChangeCover.cover A.variety.scheme (A.complexFiber j).scheme
    (A.complexPositiveProjection j) _ (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover K A.variety.scheme)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.complexPositiveCover_affine (j : K →+* ℂ)
    (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index K A.variety.scheme) :
    IsAffineOpen (A.complexPositiveCover j i) :=
  Affine.BaseChangeCover.AffineBaseChangeCover.affine j A.variety.scheme (A.complexFiber j).scheme
    (A.complexPositiveProjection j) (A.complexPositiveSquare j) _
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine K A.variety.scheme i)

private theorem complexPositiveDimension (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    (A.complexAbelianVariety j P).variety.complexDimension = A.dimension := by
  let V := (A.complexAbelianVariety j P).variety
  let : IsIntegral V.toOver.left := V.property
  let : SmoothOfRelativeDimension V.complexDimension V.structureMap :=
    V.smoothOfRelativeDimension_complexDimension
  let : SmoothOfRelativeDimension A.dimension V.structureMap :=
    (A.complexFiber j).smoothDimension
  exact IntegralComparison.Smooth.RelativeDimensionUnique.eq V.structureMap V.complexDimension A.dimension

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.numberFieldPositiveTopProduct (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (n : ℕ) (hn : n+1 = 2*A.dimension) :
    ∃ v : Fin (n+1) → A.numberFieldPositiveH 1,
      IntegralComparison.GradedPositiveProduct.product A.numberFieldPositiveCup n v ≠ 0 := by
  let : Algebra K ℂ := j.toAlgebra
  let : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap K ℂ A.variety.scheme
      (A.complexFiber j).scheme (A.complexPositiveProjection j) (A.complexPositiveSquare j).w
      (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens K A.variety.scheme) 1) :=
    IntegralComparison.Integral.CoverScalarIso.homologyMap_isIso K ℂ A.variety.scheme
      (A.complexFiber j).scheme (A.complexPositiveProjection j) (A.complexPositiveSquare j) 1
  have htop := IntegralComparison.Affine.CoverPositiveTopCup.exists_nonzero (A.complexAbelianVariety j P)
    (A.complexPositiveCover j) (A.complexPositiveCover_covers j) (A.complexPositiveCover_affine j)
    n (by rw [complexPositiveDimension A j P]; exact hn)
  exact IntegralComparison.Intrinsic.ScalarPositiveProduct.source_exists_nonzero K ℂ A.variety.scheme
    (A.complexFiber j).scheme (A.complexPositiveProjection j) (A.complexPositiveSquare j).w
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens K A.variety.scheme) n htop

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FieldPositiveTopProduct.AbelianModel
