import OAI.AlgebraicGeometry.GroupSchemes.Verschiebung
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Height One Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HeightOneTorsion.Construction

noncomputable section

/-!
A finite commutative group scheme of height one is killed by p. The
coordinate proof uses the constructed Frobenius/Verschiebung identity;
it does not replace the group scheme by its field-valued points.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry WithConv
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.GroupSchemes.Verschiebung.FiniteEtale

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [CharP k p] [PerfectRing k p]
variable [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]

/-- Height one means that coordinate Frobenius is the scalar extension
of the counit, including nilpotent coordinate functions. -/
def HopfHeightOne : Prop :=
  ∀ a : A, a ^ p = algebraMap k A ((Coalgebra.counit (R := k) a) ^ p)

theorem heightOne_convolution_power (h : HopfHeightOne p k A) (a : A) :
    ((toConv (LinearMap.id : A →ₗ[k] A)) ^ p) a =
      algebraMap k A (Coalgebra.counit (R := k) a) := by
  rw [← GroupSchemes.Verschiebung.FiniteEtale.frobenius_verschiebung p k A a, h]
  apply congrArg (algebraMap k A)
  have hv := GroupSchemes.Verschiebung.FiniteEtale.eval_verschiebung_pow p k A (1 : CartierDuality.DualAlgebra.Construction.DualCoordinate k A) a
  simpa only [one_pow, LinearMap.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply] using hv

theorem heightOne_algebra_power (h : HopfHeightOne p k A) :
    ((toConv (AlgHom.id k A) : WithConv (A →ₐ[k] A)) ^ p) = 1 := by
  apply WithConv.ofConv_injective
  ext a
  exact (congrArg (fun f : WithConv (A →ₗ[k] A) => f a)
    (AlgHom.toLinearMap_convPow (toConv (AlgHom.id k A)) p)).trans
      (heightOne_convolution_power p k A h a)

/-- The actual p-fold group endomorphism is the identity-point map. -/
theorem heightOne_scheme_power (h : HopfHeightOne p k A) :
    (𝟙 ((Spec (.of A)).asOver (Spec (.of k))) :
      (Spec (.of A)).asOver (Spec (.of k)) ⟶ (Spec (.of A)).asOver (Spec (.of k))) ^ p = 1 := by
  let e := Spec.mapMulEquiv (R := k) (S := A) (T := A)
  have he : e (toConv (AlgHom.id k A)) = 𝟙 ((Spec (.of A)).asOver (Spec (.of k))) := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  exact (congrArg (fun f => f ^ p) he).symm.trans
    ((map_pow e _ p).symm.trans
      ((congrArg e (heightOne_algebra_power p k A h)).trans e.map_one))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HeightOneTorsion.Construction
