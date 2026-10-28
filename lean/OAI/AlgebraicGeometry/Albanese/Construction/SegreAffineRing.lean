import OAI.AlgebraicGeometry.Albanese.Construction.SegreCoordinates
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Segre Affine Ring -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.SegreAffineRing

noncomputable section

open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization
open scoped TensorProduct

abbrev segreChartTensor (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :=
  Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i ⊗[ℂ] Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j

def segreTensorLeft (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Fin (m + 1) → segreChartTensor m n i j :=
  Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i (fun k => (Algebra.TensorProduct.includeLeft :
    Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i →ₐ[ℂ] segreChartTensor m n i j) (MvPolynomial.X k))

def segreTensorRight (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Fin (n + 1) → segreChartTensor m n i j :=
  Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne j (fun k => Algebra.TensorProduct.includeRight (MvPolynomial.X k))

/-- The pullback on the affine target chart at the normalized tensor coordinate. -/
def segreAffineRingMap (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j)) →ₐ[ℂ]
      segreChartTensor m n i j :=
  MvPolynomial.aeval (fun k => SegreCoordinates.segreVector (segreTensorLeft m n i j) (segreTensorRight m n i j) k.val)

/-- Row coordinates recover the nonnormalized coordinates of the first factor. -/
def segreRowIndex {m n : ℕ} (i : Fin (m + 1)) (j : Fin (n + 1))
    (k : {k : Fin (m + 1) // k ≠ i}) :
    {l : Fin (SegreCoordinates.segreDimension m n + 1) // l ≠ SegreCoordinates.segreIndexEquiv m n (i, j)} :=
  ⟨SegreCoordinates.segreIndexEquiv m n (k.val, j), fun h => k.property (congrArg Prod.fst ((SegreCoordinates.segreIndexEquiv m n).injective h))⟩

/-- Column coordinates recover the nonnormalized coordinates of the second factor. -/
def segreColumnIndex {m n : ℕ} (i : Fin (m + 1)) (j : Fin (n + 1))
    (l : {l : Fin (n + 1) // l ≠ j}) :
    {k : Fin (SegreCoordinates.segreDimension m n + 1) // k ≠ SegreCoordinates.segreIndexEquiv m n (i, j)} :=
  ⟨SegreCoordinates.segreIndexEquiv m n (i, l.val), fun h => l.property (congrArg Prod.snd ((SegreCoordinates.segreIndexEquiv m n).injective h))⟩

@[simp]
theorem segreAffineRingMap_row (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (k : {k : Fin (m + 1) // k ≠ i}) :
    segreAffineRingMap m n i j (MvPolynomial.X (segreRowIndex i j k)) =
      (Algebra.TensorProduct.includeLeft : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i →ₐ[ℂ]
        segreChartTensor m n i j) (MvPolynomial.X k) := by
  simp [segreAffineRingMap, segreRowIndex, SegreCoordinates.segreVector_pair, segreTensorLeft, segreTensorRight, k.property]

@[simp]
theorem segreAffineRingMap_column (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (l : {l : Fin (n + 1) // l ≠ j}) :
    segreAffineRingMap m n i j (MvPolynomial.X (segreColumnIndex i j l)) =
      Algebra.TensorProduct.includeRight (MvPolynomial.X l) := by
  simp [segreAffineRingMap, segreColumnIndex, SegreCoordinates.segreVector_pair, segreTensorLeft, segreTensorRight, l.property]

/-- The Segre affine coordinate map is surjective. An explicit algebra
section sends each factor's variable to its normalized row or column variable. -/
theorem segreAffineRingMap_surjective (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Function.Surjective (segreAffineRingMap m n i j) := by
  let L : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i →ₐ[ℂ]
      Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j)) :=
    MvPolynomial.aeval (fun k => MvPolynomial.X (segreRowIndex i j k))
  let R : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n j →ₐ[ℂ]
      Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j)) :=
    MvPolynomial.aeval (fun l => MvPolynomial.X (segreColumnIndex i j l))
  let s := Algebra.TensorProduct.lift L R (fun _ _ => Commute.all _ _)
  have hL : (segreAffineRingMap m n i j).comp L =
      (Algebra.TensorProduct.includeLeft : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial m i →ₐ[ℂ]
        segreChartTensor m n i j) := by
    ext k
    simp [L]
  have hR : (segreAffineRingMap m n i j).comp R = Algebra.TensorProduct.includeRight := by
    ext l
    simp [R]
  have hs : (segreAffineRingMap m n i j).comp s = AlgHom.id ℂ (segreChartTensor m n i j) := by
    apply Algebra.TensorProduct.ext
    · rw [AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeLeft, hL, AlgHom.id_comp]
    · change ((segreAffineRingMap m n i j).comp s).comp Algebra.TensorProduct.includeRight =
        (AlgHom.id ℂ (segreChartTensor m n i j)).comp Algebra.TensorProduct.includeRight
      rw [AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeRight', hR, AlgHom.id_comp]
  intro t
  exact ⟨s t, DFunLike.congr_fun hs t⟩

end

end OAI.AlgebraicGeometry.Albanese.Construction.SegreAffineRing
