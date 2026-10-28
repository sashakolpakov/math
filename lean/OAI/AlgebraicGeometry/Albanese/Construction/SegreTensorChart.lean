import OAI.AlgebraicGeometry.Albanese.Construction.SegreLocal
import OAI.AlgebraicGeometry.Albanese.Construction.SegreAffineRing

/-! # Segre Tensor Chart -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.SegreTensorChart

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

/-- The affine tensor-product chart with its coefficient-field structure. -/
abbrev segreTensorOver (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ (SegreAffineRing.segreChartTensor m n i j))))

/-- The product polynomial chart is the spectrum of the tensor product of
its two actual affine coordinate rings. -/
def segreTensorChartIso (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreLocal.projectivePairChart m n (i, j) ≅ segreTensorOver m n i j :=
  Over.isoMk (pullbackSpecIso ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j))
    (pullbackSpecIso_hom_base ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j))

@[reassoc (attr := simp)]
theorem segreTensorChartIso_inv_fst (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ((segreTensorChartIso m n i j).inv ≫ fst (ProjectiveCover.polynomialChartOver m i) (ProjectiveCover.polynomialChartOver n j)).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
        Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i →ₐ[ℂ] SegreAffineRing.segreChartTensor m n i j).toRingHom) :=
  pullbackSpecIso_inv_fst ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j)

@[reassoc (attr := simp)]
theorem segreTensorChartIso_inv_snd (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ((segreTensorChartIso m n i j).inv ≫ snd (ProjectiveCover.polynomialChartOver m i) (ProjectiveCover.polynomialChartOver n j)).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j →ₐ[ℂ] SegreAffineRing.segreChartTensor m n i j).toRingHom) :=
  pullbackSpecIso_inv_snd ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j)

/-- Pulling the first normalized coordinate tuple to the tensor chart is
the global section associated to its left tensor coordinate. -/
theorem segreTensorChart_leftTuple (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (k : Fin (m + 1)) :
    SegreLocal.leftChartTuple (segreTensorChartIso m n i j).inv k =
      (Scheme.ΓSpecIso (.of (SegreAffineRing.segreChartTensor m n i j))).inv (SegreAffineRing.segreTensorLeft m n i j k) := by
  classical
  rw [SegreLocal.leftChartTuple, segreTensorChartIso_inv_fst]
  let φ : CommRingCat.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i) ⟶ .of (SegreAffineRing.segreChartTensor m n i j) :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
      Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i →ₐ[ℂ] SegreAffineRing.segreChartTensor m n i j).toRingHom
  change (Spec.map φ).appTop ((Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i))).inv
    (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i (MvPolynomial.X k))) = _
  have h := congrArg (fun g : CommRingCat.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i) ⟶
      Γ(Spec (.of (SegreAffineRing.segreChartTensor m n i j)), ⊤) => g (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i (MvPolynomial.X k)))
    (Scheme.ΓSpecIso_inv_naturality φ)
  change (Scheme.ΓSpecIso (.of (SegreAffineRing.segreChartTensor m n i j))).inv (φ (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i (MvPolynomial.X k))) =
    (Spec.map φ).appTop ((Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i))).inv
      (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i (MvPolynomial.X k))) at h
  rw [← h]
  congr 1
  by_cases hk : k = i <;> simp [φ, SegreAffineRing.segreTensorLeft, Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize, Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne, hk]
  rfl

/-- The second normalized coordinate tuple pulls back to the right tensor
coordinates in the same way. -/
theorem segreTensorChart_rightTuple (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (k : Fin (n + 1)) :
    SegreLocal.rightChartTuple (segreTensorChartIso m n i j).inv k =
      (Scheme.ΓSpecIso (.of (SegreAffineRing.segreChartTensor m n i j))).inv (SegreAffineRing.segreTensorRight m n i j k) := by
  classical
  rw [SegreLocal.rightChartTuple, segreTensorChartIso_inv_snd]
  let φ : CommRingCat.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j) ⟶ .of (SegreAffineRing.segreChartTensor m n i j) :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j →ₐ[ℂ] SegreAffineRing.segreChartTensor m n i j).toRingHom
  change (Spec.map φ).appTop ((Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j))).inv
    (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize j (MvPolynomial.X k))) = _
  have h := congrArg (fun g : CommRingCat.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j) ⟶
      Γ(Spec (.of (SegreAffineRing.segreChartTensor m n i j)), ⊤) => g (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize j (MvPolynomial.X k)))
    (Scheme.ΓSpecIso_inv_naturality φ)
  change (Scheme.ΓSpecIso (.of (SegreAffineRing.segreChartTensor m n i j))).inv (φ (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize j (MvPolynomial.X k))) =
    (Spec.map φ).appTop ((Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j))).inv
      (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize j (MvPolynomial.X k))) at h
  rw [← h]
  congr 1
  by_cases hk : k = j <;> simp [φ, SegreAffineRing.segreTensorRight, Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize, Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne, hk]
  rfl

end

end OAI.AlgebraicGeometry.Albanese.Construction.SegreTensorChart
