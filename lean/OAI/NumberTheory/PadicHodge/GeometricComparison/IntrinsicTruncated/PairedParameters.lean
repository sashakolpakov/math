import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointedParameters
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.CommonParameterNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PairedParameters
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedParameterGeometry

/-! # Paired Parameters -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The original truncated finite shift admits a pointed frame and
two full parameter systems on one ambient projective open. The source
tuple is the literal finite pullback of the original target tuple. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PairedParameters.ParameterChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m)
attribute [local instance] MvPolynomial.gradedAlgebra
variable (U : (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n+1)).Opens)
  (hU : IsAffineOpen U)
  (D : IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) A.dimension U hU)

structure Geometry.AbelianH1Model.TruncatedPairedPointParameters where
  source : (A.truncatedShiftModel n m hm).left.affineOpens
  target : (A.truncatedModel n).scheme.left.affineOpens
  source_below : source.val ≤ (A.truncatedShiftMap n m hm) ⁻¹ᵁ
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U)
  target_below : target.val ≤ (A.truncatedTraceMorphism n).left ⁻¹ᵁ U
  source_contains : ⊤ ≤ (A.truncatedShiftIdentitySection n m hm) ⁻¹ᵁ source.val
  target_contains : ⊤ ≤ (A.truncatedIdentitySection n) ⁻¹ᵁ target.val
  reduction : (A.truncatedShiftReduction n m hm) ⁻¹ᵁ source.val =
    (A.truncatedReduction n) ⁻¹ᵁ target.val
  paired : IntegralComparison.ProjectivePoint.PairedParameters.ParameterChart.PairedData (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) A.dimension U hU D target.val
      (A.truncatedIdentityTransportedParameters n m hm source target reduction source_contains target_contains
        A.dimension (fun a => (A.truncatedShiftMap n m hm).appLE
          ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U) source.val source_below
          ((A.truncatedTraceMorphism n).left.app U (D.parameters a))))

variable (hgood : IntegralComparison.FiniteEtale.TraceBasis.Good (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
  (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
  ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U))

include hgood in
theorem Geometry.AbelianH1Model.exists_truncatedPairedPointParameters :
    Nonempty (A.TruncatedPairedPointParameters n m hm U hU D) := by
  let R := IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n
  let X := (A.truncatedModel n).scheme
  let Y := A.truncatedShiftModel n m hm
  let f := A.truncatedShiftOver n m hm
  let : IsFinite f.left := A.truncatedShiftMap_finite n m hm
  let : AlgebraicGeometry.Etale f.left := A.truncatedShiftMap_etale n m hm
  let i := A.truncatedTraceMorphism n
  let s := A.truncatedShiftIdentitySection n m hm
  let t := IntegralComparison.ProjectivePoint.ParameterSource.parameters X i (A.truncatedIdentitySection n)
    A.dimension U hU D.toParameterData
  let : Subsingleton (Spec (CommRingCat.of (ZMod q))) :=
    Ring.KrullDimLE.subsingleton_primeSpectrum (ZMod q)
  have hsf : s ≫ f.left = A.truncatedIdentitySection n := A.truncatedShiftIdentitySection_map n m hm
  let : IsClosedImmersion (s ≫ f.left) := hsf.symm ▸ inferInstance
  have hc : ⊤ ≤ (s ≫ f.left) ⁻¹ᵁ (i.left ⁻¹ᵁ U) := hsf.symm ▸ D.contains
  have ht : Ideal.span (Set.range t) = (s ≫ f.left).ker.ideal ⟨i.left ⁻¹ᵁ U,hU.preimage i.left⟩ := by
    rw [hsf]
    exact IntegralComparison.ProjectivePoint.ParameterSource.span X i (A.truncatedIdentitySection n)
      A.dimension U hU D.toParameterData
  have hr₂ : A.specialIdentitySection ≫ A.truncatedReduction n =
      Spec.map (CommRingCat.ofHom (IntegralComparison.Truncated.Witt.reduction q (ZMod q) n)) ≫ (s ≫ f.left) := by
    rw [hsf]
    exact A.truncatedIdentitySection_reduction n
  obtain ⟨E⟩ := IntegralComparison.FiniteEtale.CommonParameterNeighborhood.exists_data R X Y f s
    (A.truncatedShiftIdentitySection_over n m hm) (i.left ⁻¹ᵁ U) (hU.preimage i.left) hc hgood t
    A.specialFiber.scheme.left (A.truncatedShiftReduction n m hm) (A.truncatedReduction n) ht
    (IntegralComparison.ProjectivePoint.ParameterSource.regular X i (A.truncatedIdentitySection n)
      A.dimension U hU D.toParameterData)
    (IntegralComparison.ProjectivePoint.ParameterSource.basis X i (A.truncatedIdentitySection n)
      A.dimension U hU D.toParameterData)
    (IntegralComparison.ProjectivePoint.ParameterSource.basis_apply X i (A.truncatedIdentitySection n)
      A.dimension U hU D.toParameterData)
    (Spec.map (CommRingCat.ofHom (IntegralComparison.Truncated.Witt.reduction q (ZMod q) n)))
    (IntegralComparison.Truncated.SectionPuncture.reduction_surjective q (ZMod q) n)
    A.specialIdentitySection (A.truncatedShiftIdentitySection_reduction n m hm).symm hr₂
  have hc₂ : ⊤ ≤ (A.truncatedIdentitySection n) ⁻¹ᵁ E.target.val := hsf ▸ E.target_contains
  let b₀ : Fin A.dimension → Γ(Y.left,E.source.val) := fun a =>
    f.left.appLE (i.left ⁻¹ᵁ U) E.source.val E.source_le (i.left.app U (D.parameters a))
  let t' := A.truncatedIdentityTransportedParameters n m hm E.source E.target E.reduction
    E.source_contains hc₂ A.dimension b₀
  have ht' : Ideal.span (Set.range t') = (A.truncatedIdentitySection n).ker.ideal E.target :=
    A.truncatedIdentityTransportedParameters_span n m hm E.source E.target E.reduction
      E.source_contains hc₂ A.dimension b₀ E.ideal
  have hreg' : RingTheory.Sequence.IsWeaklyRegular Γ(X.left,E.target.val) (List.ofFn t') :=
    IntegralComparison.TruncatedModel.PointedParameterGeometry.regular q (ZMod q) n Y X A.specialFiber.scheme
      (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
      (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
      E.source E.target E.reduction s (A.truncatedShiftIdentitySection_over n m hm)
      (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
      A.specialIdentitySection A.specialIdentitySection_over
      (A.truncatedShiftIdentitySection_reduction n m hm).symm (A.truncatedIdentitySection_reduction n)
      E.source_contains hc₂ A.dimension b₀ E.regular
  let b' := IntegralComparison.TruncatedModel.PointedParameterGeometry.basis q (ZMod q) n Y X A.specialFiber.scheme
    (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
    E.source E.target E.reduction s (A.truncatedShiftIdentitySection_over n m hm)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    A.specialIdentitySection A.specialIdentitySection_over
    (A.truncatedShiftIdentitySection_reduction n m hm).symm (A.truncatedIdentitySection_reduction n)
    E.source_contains hc₂ A.dimension E.basis
  have hb' (a : Fin A.dimension) : b' a = KaehlerDifferential.D R Γ(X.left,E.target.val) (t' a) :=
    IntegralComparison.TruncatedModel.PointedParameterGeometry.basis_apply q (ZMod q) n Y X A.specialFiber.scheme
      (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
      (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
      E.source E.target E.reduction s (A.truncatedShiftIdentitySection_over n m hm)
      (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
      A.specialIdentitySection A.specialIdentitySection_over
      (A.truncatedShiftIdentitySection_reduction n m hm).symm (A.truncatedIdentitySection_reduction n)
      E.source_contains hc₂ A.dimension b₀ E.basis E.basis_apply a
  obtain ⟨P⟩ := IntegralComparison.ProjectivePoint.PairedParameters.ParameterChart.exists_paired X i (A.truncatedIdentitySection n) A.dimension U hU D E.target.val t'
    (A.truncatedIdentitySection_over n) E.target.property hc₂ ht' hreg' b' hb'
  exact ⟨{
    source := E.source
    target := E.target
    source_below := E.source_le
    target_below := E.target_le
    source_contains := E.source_contains
    target_contains := hc₂
    reduction := E.reduction
    paired := P
  }⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
