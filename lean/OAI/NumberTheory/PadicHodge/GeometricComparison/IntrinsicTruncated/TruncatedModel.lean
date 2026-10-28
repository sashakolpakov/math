import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AbelianReductionSequence
import OAI.NumberTheory.PadicHodge.GeometricComparison.Residue
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt
import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFiberAmpleness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-! # Truncated Model -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The actual good-reduction abelian model at a finite Witt level, with
its original special fiber as a surjective closed reduction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace IntrinsicTruncated.TruncatedModel.NativeTruncatedBase

variable (q : ℕ) [Fact q.Prime] (n : ℕ)
abbrev Ring := IntegralComparison.Truncated.Witt.Ring q (ZMod q) n

def coefficient : ℤ_[q] →+* Ring q n :=
  (IntegralComparison.Truncated.Witt.quotient q (ZMod q) n).comp (WittVector.equiv q).symm.toRingHom

abbrev reduction : Ring q n →+* ZMod q := IntegralComparison.Truncated.Witt.reduction q (ZMod q) n

theorem reduction_coefficient : (reduction q n).comp (coefficient q n) = PadicInt.toZMod :=
  Residue.PadicBase.ringHom_eq_toZMod q _

theorem reduction_kernel : RingHom.ker (reduction q n) = Ideal.span {(q : Ring q n)} := by
  rw [IntegralComparison.Truncated.Witt.reduction_kernel]
  change (Ideal.span {(q : WittVector q (ZMod q))}).map _ = _
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

theorem kernel_nilpotent (a : Ring q n) (ha : a ∈ RingHom.ker (reduction q n)) : IsNilpotent a := by
  rw [reduction_kernel, Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  exact ⟨n + 1, by rw [mul_pow, IntegralComparison.Truncated.Witt.prime_power_zero, zero_mul]⟩

instance reduction_closed : IsClosedImmersion (Spec.map (CommRingCat.ofHom (reduction q n))) :=
  IsClosedImmersion.spec_of_surjective _ (IntegralComparison.Truncated.Witt.reduction_surjective q (ZMod q) n)

instance reduction_surjective : Surjective (Spec.map (CommRingCat.ofHom (reduction q n))) :=
  IntegralComparison.NilpotentFiberAmpleness.reduction_surjective _
    (IntegralComparison.Truncated.Witt.reduction_surjective q (ZMod q) n) (kernel_nilpotent q n)

end IntrinsicTruncated.TruncatedModel.NativeTruncatedBase

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.truncatedModel (n : ℕ) := A.integral.pullback
  (Geometry.scalarBaseMap (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.coefficient q n))

def Geometry.AbelianH1Model.truncatedToIntegral (n : ℕ) : (A.truncatedModel n).scheme.left ⟶ A.integral.scheme.left :=
  pullback.fst _ _

def Geometry.AbelianH1Model.truncatedReduction (n : ℕ) : A.specialFiber.scheme.left ⟶ (A.truncatedModel n).scheme.left :=
  pullback.lift A.integralReductionMorphism
    (A.specialFiber.scheme.hom ≫ Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n))) (by
      rw [Category.assoc, Geometry.scalarBaseMap, ← Spec.map_comp]
      change A.integralReductionMorphism ≫ A.integral.scheme.hom =
        A.specialFiber.scheme.hom ≫ Spec.map
          (CommRingCat.ofHom ((IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n).comp (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.coefficient q n)))
      rw [IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction_coefficient]
      exact A.integralReductionSquare.w)

@[reassoc] theorem Geometry.AbelianH1Model.truncatedReduction_toIntegral (n : ℕ) :
    A.truncatedReduction n ≫ A.truncatedToIntegral n = A.integralReductionMorphism :=
  pullback.lift_fst _ _ _

@[reassoc] theorem Geometry.AbelianH1Model.truncatedReduction_base (n : ℕ) :
    A.truncatedReduction n ≫ (A.truncatedModel n).scheme.hom =
      A.specialFiber.scheme.hom ≫ Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)) :=
  pullback.lift_snd _ _ _

theorem Geometry.AbelianH1Model.truncatedReductionSquare (n : ℕ) :
    IsPullback (A.truncatedReduction n) A.specialFiber.scheme.hom
      (A.truncatedModel n).scheme.hom
      (Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n))) := by
  have hp := A.integralReductionSquare
  have hbase : Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)) ≫
      Geometry.scalarBaseMap (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.coefficient q n) = Geometry.scalarBaseMap PadicInt.toZMod := by
    rw [Geometry.scalarBaseMap, ← Spec.map_comp]
    exact congrArg (fun f : ℤ_[q] →+* ZMod q => Spec.map (CommRingCat.ofHom f))
      (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction_coefficient q n)
  have hwhole : IsPullback (A.truncatedReduction n ≫ A.truncatedToIntegral n)
      A.specialFiber.scheme.hom A.integral.scheme.hom
      (Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)) ≫
        Geometry.scalarBaseMap (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.coefficient q n)) := by
    rw [A.truncatedReduction_toIntegral, hbase]
    exact hp
  exact hwhole.of_right (A.truncatedReduction_base n) (IsPullback.of_hasPullback _ _)

instance Geometry.AbelianH1Model.truncatedReduction_closed (n : ℕ) : IsClosedImmersion (A.truncatedReduction n) :=
  IsClosedImmersion.isStableUnderBaseChange.of_isPullback (A.truncatedReductionSquare n).flip
    (inferInstanceAs (IsClosedImmersion (Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)))))

instance Geometry.AbelianH1Model.truncatedReduction_surjective (n : ℕ) : Surjective (A.truncatedReduction n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
    (A.truncatedReductionSquare n).flip inferInstance

def Geometry.AbelianH1Model.truncatedReductionHomeomorph (n : ℕ) :
    A.specialFiber.scheme.left ≃ₜ (A.truncatedModel n).scheme.left :=
  (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(A.truncatedReduction n).isClosedEmbedding.isEmbedding, (A.truncatedReduction n).surjective⟩).homeomorph

theorem Geometry.AbelianH1Model.truncated_prime_power_zero (n : ℕ) (U : (A.truncatedModel n).scheme.left.Opens) :
    (q : Γ((A.truncatedModel n).scheme.left, U)) ^ (n + 1) = 0 := by
  have h := congrArg (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap
    (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme U)
    (IntegralComparison.Truncated.Witt.prime_power_zero q (ZMod q) n)
  simpa only [map_pow, map_natCast, map_zero] using h

theorem Geometry.AbelianH1Model.truncatedReduction_kernel (n : ℕ) (U : (A.truncatedModel n).scheme.left.Opens)
    (hU : IsAffineOpen U) :
    RingHom.ker ((A.truncatedReduction n).app U).hom = Ideal.span {(q : Γ((A.truncatedModel n).scheme.left, U))} := by
  let : Algebra (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (ZMod q) := (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n).toAlgebra
  have h := AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing.BaseAffineReductionRing.kernel_principal
    (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (ZMod q) (A.truncatedModel n).scheme A.specialFiber.scheme
    (A.truncatedReduction n) (A.truncatedReductionSquare n) U hU
    (IntegralComparison.Truncated.Witt.reduction_surjective q (ZMod q) n) (q : IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction_kernel q n)
  simpa only [map_natCast] using h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
