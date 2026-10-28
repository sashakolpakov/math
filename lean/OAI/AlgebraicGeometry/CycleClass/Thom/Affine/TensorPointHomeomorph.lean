import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphScheme
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PresentationImmersion

/-! # Tensor Point Homeomorph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.TensorPointHomeomorph.Constructions

noncomputable section

/-! The actual tensor-product characters identify the affine scheme graph with the usual graph in a product of complex point spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphRingMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphScheme.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PresentationImmersion.Constructions

variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]

def affineTensorHomeomorph :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (R ⊗[ℂ] S) ≃ₜ (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R × Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) where
  toFun x := (x.comp Algebra.TensorProduct.includeLeft, x.comp Algebra.TensorProduct.includeRight)
  invFun := Scheme.PointProduct.Constructions.affineTensorPair R S
  left_inv x := by
    apply Algebra.TensorProduct.ext
    · exact Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)
    · exact Algebra.TensorProduct.lift_comp_includeRight' _ _ (fun _ _ => Commute.all _ _)
  right_inv x := by
    exact Prod.ext (Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _))
      (Algebra.TensorProduct.lift_comp_includeRight' _ _ (fun _ _ => Commute.all _ _))
  continuous_toFun :=
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] S)).continuous.prodMk
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] R ⊗[ℂ] S)).continuous
  continuous_invFun := Scheme.PointProduct.Constructions.affineTensorPair_continuous R S

omit [CommRing S] [Algebra ℂ S] in
def affineGraphHomeomorph (n : ℕ) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (R ⊗[ℂ] MvPolynomial (Fin n) ℂ) ≃ₜ
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R × (Fin n → ℂ)) :=
  (affineTensorHomeomorph R (MvPolynomial (Fin n) ℂ)).trans
    ((Homeomorph.refl (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R)).prodCongr (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph (Fin n)))

variable {R S}

theorem affineTensorHomeomorph_graph {A : Type} [CommRing A] [Algebra ℂ A]
    (h : R →ₐ[ℂ] A) (f : S →ₐ[ℂ] A) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    affineTensorHomeomorph R S (x.comp (GraphRingMap.Constructions.graphRingMap h f)) = (x.comp h, x.comp f) := by
  apply Prod.ext
  · change (x.comp (GraphRingMap.Constructions.graphRingMap h f)).comp Algebra.TensorProduct.includeLeft = _
    rw [AlgHom.comp_assoc, GraphRingMap.Constructions.graphRingMap_left]
  · change (x.comp (GraphRingMap.Constructions.graphRingMap h f)).comp Algebra.TensorProduct.includeRight = _
    rw [AlgHom.comp_assoc, GraphRingMap.Constructions.graphRingMap_right]

omit [CommRing S] [Algebra ℂ S] in
theorem affineGraphHomeomorph_graph {A : Type} [CommRing A] [Algebra ℂ A] {n : ℕ}
    (h : R →ₐ[ℂ] A) (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    affineGraphHomeomorph R n (x.comp (GraphRingMap.Constructions.graphRingMap h f)) =
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h x, PresentationImmersion.Constructions.presentationCoordinates f x) := by
  change ((Homeomorph.refl _).prodCongr (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph (Fin n)))
    (affineTensorHomeomorph R (MvPolynomial (Fin n) ℂ) (x.comp (GraphRingMap.Constructions.graphRingMap h f))) = _
  rw [affineTensorHomeomorph_graph]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.TensorPointHomeomorph.Constructions
