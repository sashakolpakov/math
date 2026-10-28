import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelScalar
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-! # Scalar Characters -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.ScalarCharacters

noncomputable section

/-! Multiplicative global functions on an affine group scheme are
group-like elements of its actual coordinate Hopf algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (k R : Type u) [CommRing k] [CommRing R] [Bialgebra k R]

theorem specScalar_evaluation (s : Γ(Spec (.of R), ⊤))
    (T : Type u) [CommRing T] [Algebra k T] (a : WithConv (R →ₐ[k] T)) :
    (Scheme.ΓSpecIso (.of T)).hom
      ((Spec.mapMulEquiv (R := k) a).left.appTop s) =
      a ((Scheme.ΓSpecIso (.of R)).hom s) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom a.ofConv.toRingHom)) s

variable (s : Γ(Spec (.of R), ⊤))
variable (hone : ∀ (T : Over (Spec (.of k))),
  (1 : T ⟶ (Spec (.of R)).asOver (Spec (.of k))).left.appTop s = 1)
variable (hmul : ∀ (T : Over (Spec (.of k)))
  (a b : T ⟶ (Spec (.of R)).asOver (Spec (.of k))),
  (a * b).left.appTop s = a.left.appTop s * b.left.appTop s)

include hmul in
theorem multiplicativeScalar_convMul (T : Type u) [CommRing T] [Algebra k T]
    (a b : WithConv (R →ₐ[k] T)) :
    (a * b) ((Scheme.ΓSpecIso (.of R)).hom s) =
      a ((Scheme.ΓSpecIso (.of R)).hom s) * b ((Scheme.ΓSpecIso (.of R)).hom s) := by
  have hp : (Spec.mapMulEquiv (R := k) (a * b)).left.appTop s =
      (Spec.mapMulEquiv (R := k) a).left.appTop s *
        (Spec.mapMulEquiv (R := k) b).left.appTop s :=
    (congrArg (fun c => c.left.appTop s)
      ((Spec.mapMulEquiv (R := k) (S := R) (T := T)).map_mul a b)).trans
        (hmul _ _ _)
  exact (specScalar_evaluation k R s T (a * b)).symm.trans
    ((congrArg (fun z : Γ(Spec (.of T), ⊤) => (Scheme.ΓSpecIso (.of T)).hom z) hp).trans
      ((map_mul (Scheme.ΓSpecIso (.of T)).hom.hom _ _).trans
        (congrArg₂ (· * ·) (specScalar_evaluation k R s T a) (specScalar_evaluation k R s T b))))

include hone hmul in
def groupLikeOfMultiplicativeScalar : GroupLike k R := by
  let r : R := (Scheme.ΓSpecIso (.of R)).hom s
  refine ⟨r, ?_, ?_⟩
  · have hp : (Spec.mapMulEquiv (R := k) (S := R) (T := k) 1).left.appTop s = 1 :=
      (congrArg (fun c => c.left.appTop s)
        (Spec.mapMulEquiv (R := k) (S := R) (T := k)).map_one).trans (hone _)
    exact (specScalar_evaluation k R s k 1).symm.trans
      ((congrArg (fun z : Γ(Spec (.of k), ⊤) => (Scheme.ΓSpecIso (.of k)).hom z) hp).trans
        (map_one (Scheme.ΓSpecIso (.of k)).hom.hom))
  · let a : WithConv (R →ₐ[k] R ⊗[k] R) := WithConv.toConv Algebra.TensorProduct.includeLeft
    let b : WithConv (R →ₐ[k] R ⊗[k] R) := WithConv.toConv Algebra.TensorProduct.includeRight
    have hl : Algebra.TensorProduct.lift a.ofConv b.ofConv (fun _ _ => .all ..) =
        AlgHom.id k (R ⊗[k] R) := by
      apply AlgHom.toLinearMap_injective
      apply TensorProduct.ext'
      intro x y
      simp [a, b]
    have h := multiplicativeScalar_convMul k R s hmul (R ⊗[k] R) a b
    rw [AlgHom.convMul_apply, hl] at h
    change Coalgebra.comul r = (r ⊗ₜ[k] 1) * (1 ⊗ₜ[k] r) at h
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using h

variable {k R}

theorem groupLikeOfMultiplicativeScalar_injective (s t : Γ(Spec (.of R), ⊤))
    (hsone htone) (hsmul htmul)
    (h : groupLikeOfMultiplicativeScalar k R s (hone := hsone) (hmul := hsmul) =
      groupLikeOfMultiplicativeScalar k R t (hone := htone) (hmul := htmul)) : s = t := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).injective
  exact congrArg GroupLike.val h

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.ScalarCharacters
