import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneComponentScales
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneBallCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ArchFrame

/-! # One Frame Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneFrameComparison.Multiplicity

noncomputable section

/-! The original native period frame becomes the AdelicTheta geometric frame
after an explicit constant invertible diagonal change of its columns. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)

theorem nativeOneComponents_active (w : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    (fun j => (OneComplexComponents.Quadratic.oneComplexComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) w
      P.distinguished).1 (j, 0),
     fun j => (OneComplexComponents.Quadratic.oneComplexComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) w
      P.distinguished).2 (j, 0)) =
      NormalizedFrame.normalizeWeightedPhase (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ)
        (OneDiagonalNormalizer.Multiplicity.nativeOneScale E P v P.distinguished : ℂ) (w P.distinguished) := by
  have hd : Multiplicity.Period.nativeCompactSigns E P v P.distinguished = true := by
    simp only [Multiplicity.Period.nativeCompactSigns, Multiplicity.Period.nativeArchLabel_active E P hμ, inv_one, hv]
  apply Prod.ext <;> funext j
  · rw [OneComponentScales.Multiplicity.nativeOneComponents_fst]
    fin_cases j <;> simp [NormalizedFrame.normalizeWeightedPhase, OneComponentScales.Multiplicity.nativeOneComponentScale,
      Matrix.mulVec_diagonal]
  · rw [OneComponentScales.Multiplicity.nativeOneComponents_snd]
    fin_cases j <;> simp [NormalizedFrame.normalizeWeightedPhase, OneComponentScales.Multiplicity.nativeOneComponentScale, hd,
      Matrix.mulVec_diagonal]

def nativeOneFrameCoefficients (u : Fin s × Fin 3 → ℂ) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) → ℂ :=
  fun ij => OneComponentScales.Multiplicity.nativeOneFrameScale E P v ij.1 ij.2.1 * u (ij.1, ij.2.1)

theorem nativeOneFrameCoefficients_bijective :
    Function.Bijective (nativeOneFrameCoefficients E P hP hμ hs v hv) := by
  constructor
  · intro u w h
    funext ⟨i, j⟩
    exact mul_left_cancel₀ (OneComponentScales.Multiplicity.nativeOneFrameScale_ne_zero E P hP hμ v i j)
      (congrFun h (i, j, 0))
  · intro w
    refine ⟨fun ij => w (ij.1, ij.2, 0) / OneComponentScales.Multiplicity.nativeOneFrameScale E P v ij.1 ij.2, ?_⟩
    funext ⟨i, j, k⟩
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    exact mul_div_cancel₀ _ (OneComponentScales.Multiplicity.nativeOneFrameScale_ne_zero E P hP hμ v i j)

theorem nativeOne_geometricFrame
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) (u : Fin s × Fin 3 → ℂ) :
    OneComplexComponents.Quadratic.oneComplexComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv)
      (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P)) P.distinguished
        (Multiplicity.Period.nativeCompactSigns E P v) z.val u) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z)
        (nativeOneFrameCoefficients E P hP hμ hs v hv u) := by
  let w := RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P)) P.distinguished
    (Multiplicity.Period.nativeCompactSigns E P v) z.val u
  have hdist : (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).distinguished = P.distinguished := rfl
  refine funext (fun i : Fin s => ?_)
  by_cases hi : i = P.distinguished
  · subst i
    have hn := nativeOneComponents_active E P hP hμ hs v hv w
    have hw : w P.distinguished =
        UnitaryFrameAction.weightedFrame (P.embeddings P.distinguished P.b) z.val
          (fun j => u (P.distinguished, j)) := by
      change Geometry.ComplexBall.PrescribedSignsB.placeFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P)) P.distinguished
        (Multiplicity.Period.nativeCompactSigns E P v) z.val P.distinguished _ = _
      rw [Geometry.ComplexBall.PrescribedSignsB.placeFrame, ite_eq_left rfl, Intrinsic.ArchFrame.native_localFrame_weighted]
      rfl
    rw [hw, OneBallCoordinates.Multiplicity.nativeOne_active_coefficient E P hP hμ,
      NormalizedFrame.weightedFrame_normalized _ _
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (OneDiagonalNormalizer.Multiplicity.nativeOneRadius_pos E P hP hμ P.distinguished)))] at hn
    apply Prod.ext <;> funext ⟨j, k⟩
    · have hk : k = 0 := Subsingleton.elim _ _
      subst k
      exact (congrFun (congrArg Prod.fst hn) j).trans (by
        simp only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, ite_eq_left hdist.symm]
        simp [nativeOneFrameCoefficients, OneComponentScales.Multiplicity.nativeOneFrameScale,
          NormalizedFrame.lineAnnihilatorFrame, OneBallCoordinates.Multiplicity.nativeOneBallPoint, mul_comm,
          Matrix.mulVec_diagonal])
    · have hk : k = 0 := Subsingleton.elim _ _
      subst k
      exact (congrFun (congrArg Prod.snd hn) j).trans (by
        simp only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, ite_eq_left hdist.symm]
        simp [nativeOneFrameCoefficients, OneComponentScales.Multiplicity.nativeOneFrameScale,
          NormalizedFrame.lineAnnihilatorFrame, OneBallCoordinates.Multiplicity.nativeOneBallPoint, mul_comm,
          Matrix.mulVec_diagonal])
  · have hne : i ≠ (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).distinguished :=
      fun h => hi (h.trans hdist)
    have hw : w i = if Multiplicity.Period.nativeCompactSigns E P v i then
        (0, fun j => u (i, j)) else (fun j => u (i, j), 0) := by
      simp [w, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame, Geometry.ComplexBall.PrescribedSignsB.globalFrame, Geometry.ComplexBall.PrescribedSignsB.placeFrame, hi]
      split_ifs <;> rfl
    apply Prod.ext <;> funext ⟨j, k⟩
    · have hk : k = 0 := Subsingleton.elim _ _
      subst k
      refine (OneComponentScales.Multiplicity.nativeOneComponents_fst E P hP hμ hs v hv w i j).trans ?_
      rw [hw]
      simp only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame]
      rw [Intrinsic.OneCoordinates.Multiplicity.nativeOneBall_sign E P hP hμ hs v hv i]
      cases hd : Multiplicity.Period.nativeCompactSigns E P v i <;> fin_cases j <;>
        simp [nativeOneFrameCoefficients, OneComponentScales.Multiplicity.nativeOneFrameScale, OneComponentScales.Multiplicity.nativeOneComponentScale, hi, hd] <;>
        intro h <;> exact (hne h).elim
    · have hk : k = 0 := Subsingleton.elim _ _
      subst k
      refine (OneComponentScales.Multiplicity.nativeOneComponents_snd E P hP hμ hs v hv w i j).trans ?_
      rw [hw]
      simp only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame]
      rw [Intrinsic.OneCoordinates.Multiplicity.nativeOneBall_sign E P hP hμ hs v hv i]
      cases hd : Multiplicity.Period.nativeCompactSigns E P v i <;> fin_cases j <;>
        simp [nativeOneFrameCoefficients, OneComponentScales.Multiplicity.nativeOneFrameScale, OneComponentScales.Multiplicity.nativeOneComponentScale, hi, hd] <;>
        intro h <;> exact (hne h).elim

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneFrameComparison.Multiplicity
