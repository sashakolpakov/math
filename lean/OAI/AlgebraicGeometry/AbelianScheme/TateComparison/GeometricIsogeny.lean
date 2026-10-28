import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Isogeny
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny

/-! # Geometric Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricIsogeny

noncomputable section

/-! Apply the finite-kernel construction to actual geometric points of
an abelian-scheme isogeny. Its rational Tate map is a linear isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  {k : Type u} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  (q : ℕ) [Fact q.Prime]

def geometricTateIsogenyEquiv (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) :
    Rational.rationalTateModule A.scheme (Over.mk b) q ≃ₗ[ℚ_[q]]
      Rational.rationalTateModule B.scheme (Over.mk b) q := by
  let φ := (A.mapPoints B f.hom (Over.mk b)).toAdditive
  have hf : Function.Surjective φ := FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricPoints_surjective f b
  have hk : Finite φ.ker := by
    have : Finite (f.kernelAt (Over.mk b)) := FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricKernel_finite f b
    exact Finite.of_equiv (f.kernelAt (Over.mk b)) {
      toFun x := ⟨Additive.ofMul x.val, x.property⟩
      invFun x := ⟨x.val.toMul, x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact Isogeny.Tate.rationalEquivOfFiniteKernel q φ hf

theorem geometricTateIsogenyEquiv_toLinearMap (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) :
    (geometricTateIsogenyEquiv b q f).toLinearMap =
      Rational.rationalTateMap (T := Over.mk b) (q := q) f.hom := rfl

theorem rationalTateMap_isogeny_bijective (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) :
    Function.Bijective (Rational.rationalTateMap (T := Over.mk b) (q := q) f.hom) :=
  (geometricTateIsogenyEquiv b q f).bijective

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricIsogeny
