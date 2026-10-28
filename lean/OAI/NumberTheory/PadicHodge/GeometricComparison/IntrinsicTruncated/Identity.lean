import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.Connected
import OAI.NumberTheory.PadicHodge.IntegralComparison.GroupBaseChangeIdentity
import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentAffineSections

/-! # Identity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The original special-fiber identity section reduces from the
actual identity section of every truncated abelian model. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

namespace IntrinsicTruncated.Identity.NativeTruncatedBase
variable (q : ℕ) [Fact q.Prime] (n : ℕ)

theorem reduction_ker_nilpotent :
    IsNilpotent (Spec.map (CommRingCat.ofHom (TruncatedModel.NativeTruncatedBase.reduction q n))).ker := by
  apply IntegralComparison.NilpotentAffineSections.spec
  refine ⟨n + 1, ?_⟩
  change RingHom.ker (TruncatedModel.NativeTruncatedBase.reduction q n) ^ (n + 1) = 0
  calc
    _ = (Ideal.span {(q : TruncatedModel.NativeTruncatedBase.Ring q n)}) ^ (n + 1) :=
      congrArg (fun I : Ideal (TruncatedModel.NativeTruncatedBase.Ring q n) => I ^ (n + 1)) (TruncatedModel.NativeTruncatedBase.reduction_kernel q n)
    _ = Ideal.span {(q : TruncatedModel.NativeTruncatedBase.Ring q n) ^ (n + 1)} := Ideal.span_singleton_pow _ _
    _ = 0 := Ideal.span_singleton_eq_bot.mpr (IntegralComparison.Truncated.Witt.prime_power_zero q (ZMod q) n)

end IntrinsicTruncated.Identity.NativeTruncatedBase

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.specialIdentitySection : Spec (.of (ZMod q)) ⟶ A.specialFiber.scheme.left :=
  (1 : Over.mk (𝟙 (Spec (.of (ZMod q)))) ⟶ A.specialFiber.scheme).left

theorem Geometry.AbelianH1Model.specialIdentitySection_over : A.specialIdentitySection ≫ A.specialFiber.scheme.hom = 𝟙 _ :=
  (1 : Over.mk (𝟙 (Spec (.of (ZMod q)))) ⟶ A.specialFiber.scheme).w

theorem Geometry.AbelianH1Model.truncatedIdentitySection_reduction (n : ℕ) :
    A.specialIdentitySection ≫ A.truncatedReduction n =
      Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)) ≫ A.truncatedIdentitySection n := by
  apply pullback.hom_ext
  · change (A.specialIdentitySection ≫ A.truncatedReduction n) ≫ A.truncatedToIntegral n =
      (Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)) ≫
        A.truncatedIdentitySection n) ≫ A.truncatedToIntegral n
    rw [Category.assoc, A.truncatedReduction_toIntegral]
    have h₀ := IntegralComparison.GroupBaseChangeIdentity.projection A.integral.scheme (Geometry.scalarBaseMap PadicInt.toZMod)
    have hn := IntegralComparison.GroupBaseChangeIdentity.projection A.integral.scheme
      (Geometry.scalarBaseMap (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.coefficient q n))
    change A.specialIdentitySection ≫ A.integralReductionMorphism =
      Geometry.scalarBaseMap PadicInt.toZMod ≫ (1 : Over.mk (𝟙 _) ⟶ A.integral.scheme).left at h₀
    change A.truncatedIdentitySection n ≫ A.truncatedToIntegral n =
      Geometry.scalarBaseMap (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.coefficient q n) ≫
        (1 : Over.mk (𝟙 _) ⟶ A.integral.scheme).left at hn
    rw [h₀, Category.assoc, hn, ← Category.assoc, Geometry.scalarBaseMap, Geometry.scalarBaseMap, ← Spec.map_comp]
    congr 2
    exact congrArg CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction_coefficient q n).symm
  · change (A.specialIdentitySection ≫ A.truncatedReduction n) ≫ (A.truncatedModel n).scheme.hom =
      (Spec.map (CommRingCat.ofHom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.reduction q n)) ≫
        A.truncatedIdentitySection n) ≫ (A.truncatedModel n).scheme.hom
    rw [Category.assoc, A.truncatedReduction_base, ← Category.assoc, A.specialIdentitySection_over,
      Category.id_comp, Category.assoc, A.truncatedIdentitySection_over, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
