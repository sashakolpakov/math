import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ProductBaseCoefficients
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientBaseChangeAssociativity

/-! # Product Coefficient Assembly -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ProductCoefficientAssembly

noncomputable section

/-! Coefficient ideals on two affine base changes combine on their product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
variable {X : Scheme.{u}} (f : X ⟶ Spec R) [Flat f] (K : X.IdealSheafData)

theorem affineIdealCoefficient_product_assembly (I : Ideal A) (J : Ideal B)
    (hI : Affine.IdealCoefficientTests.IsAffineIdealCoefficient A
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A))))
      (K.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R A))))) I)
    (hJ : Affine.IdealCoefficientTests.IsAffineIdealCoefficient B
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R B))))
      (K.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R B))))) J) :
    Affine.IdealCoefficientTests.IsAffineIdealCoefficient (CommRingCat.of (A × B))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (A × B)))))
      (K.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (A × B)))))) (I.prod J) := by
  let C := CommRingCat.of (A × B)
  let φ : R ⟶ C := CommRingCat.ofHom (algebraMap R C)
  let a : C ⟶ A := CommRingCat.ofHom (RingHom.fst A B)
  let b : C ⟶ B := CommRingCat.ofHom (RingHom.snd A B)
  have ha : φ ≫ a = CommRingCat.ofHom (algebraMap R A) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    rfl
  have hb : φ ≫ b = CommRingCat.ofHom (algebraMap R B) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    rfl
  apply ProductBaseCoefficients.affineIdealCoefficient_product_base A B
  · apply CoefficientBaseChangeAssociativity.affineIdealCoefficient_iterated_baseChange f K φ a I
    rw [ha]
    exact hI
  · apply CoefficientBaseChangeAssociativity.affineIdealCoefficient_iterated_baseChange f K φ b J
    rw [hb]
    exact hJ

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ProductCoefficientAssembly
