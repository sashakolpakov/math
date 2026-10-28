import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneComplexComponents
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneDiagonalNormalizer

/-! # One Component Scales -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneComponentScales.Multiplicity

noncomputable section

/-! Explicit entries of the paired native-to-AdelicTheta component map. -/

open scoped Classical _root_.NumberField _root_.Matrix Kronecker
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)

def nativeOneComponentScale (i : Fin s) (j : Fin 3) : ℂ :=
  (![OneDiagonalNormalizer.Multiplicity.nativeOneScale E P v i, OneDiagonalNormalizer.Multiplicity.nativeOneScale E P v i,
    OneDiagonalNormalizer.Multiplicity.nativeOneScale E P v i * OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P i] j : ℂ)

theorem nativeOneComponents_fst (w : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) (i : Fin s) (j : Fin 3) :
    (OneComplexComponents.Quadratic.oneComplexComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) w i).1 (j, 0) =
      nativeOneComponentScale E P v i j * (w i).1 j := by
  change (((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).basisV i).inv ⊗ₖ
    ((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).basisP i).inv).mulVec
      (fun ij => (w i).1 ij.1) (j, 0) = _
  rw [OneDiagonalNormalizer.Multiplicity.nativeOneTensorNormalizer, Matrix.mulVec_diagonal]
  rfl

theorem nativeOneComponents_snd (w : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) (i : Fin s) (j : Fin 3) :
    (OneComplexComponents.Quadratic.oneComplexComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) w i).2 (j, 0) =
      (if i = P.distinguished ∧ j = 2 then (-1 : ℂ) else 1) *
        (if Multiplicity.Period.nativeCompactSigns E P v i then (-1 : ℂ) else 1) *
          (nativeOneComponentScale E P v i j * (w i).2 j) := by
  change (if i = P.distinguished ∧ j = 2 then (-1 : ℂ) else 1) *
    (if (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).positive i 0 then (1 : ℂ) else -1) *
      ((((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).basisV i).inv ⊗ₖ
        ((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).basisP i).inv).map star).mulVec
          (fun ij => (w i).2 ij.1) (j, 0) = _
  rw [OneDiagonalNormalizer.Multiplicity.nativeOneTensorNormalizer, Matrix.map_diagonal_star, Matrix.mulVec_diagonal,
    Intrinsic.OneCoordinates.Multiplicity.nativeOneBall_sign]
  cases Multiplicity.Period.nativeCompactSigns E P v i <;>
    simp [nativeOneComponentScale]

def nativeOneFrameScale (i : Fin s) : Fin 3 → ℂ :=
  let c : ℂ := OneDiagonalNormalizer.Multiplicity.nativeOneScale E P v i
  let r : ℂ := OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P i
  if i = P.distinguished then ![c * r, -c, -c]
  else if Multiplicity.Period.nativeCompactSigns E P v i then ![-c, -c, -(c * r)] else ![c, c, c * r]

include hP hμ in
theorem nativeOneFrameScale_ne_zero (i : Fin s) (j : Fin 3) :
    nativeOneFrameScale E P v i j ≠ 0 := by
  have hc : (OneDiagonalNormalizer.Multiplicity.nativeOneScale E P v i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (OneDiagonalNormalizer.Multiplicity.nativeOneScale_pos E P hP hμ v i))
  have hr : (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (OneDiagonalNormalizer.Multiplicity.nativeOneRadius_pos E P hP hμ i))
  unfold nativeOneFrameScale
  split_ifs <;> fin_cases j <;> simp [hc, hr]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneComponentScales.Multiplicity
