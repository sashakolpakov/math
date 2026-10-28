import OAI.RepresentationTheory.Theta.Adelic.BallGroupComparison
import OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall

/-! # Ball Proper -/

namespace OAI.RepresentationTheory.Theta.Adelic.BallProper

noncomputable section

/-! The actual AdelicTheta ball action is transitive and proper, by the
explicit coordinate identification with the proved ArithmeticQuotient action. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.BallGroupComparison

def ballHomeomorph : BallNatural.Ball ≃ₜ Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (-1) where
  toFun z := ⟨z.val, by
    change Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < -(-1 : ℂ).re
    have hz : Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < 1 := z.property
    simpa only [Complex.neg_re, Complex.one_re, neg_neg] using hz⟩
  invFun z := ⟨z.val, by
    change Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < 1
    have hz := z.property
    change Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < -(-1 : ℂ).re at hz
    simpa only [Complex.neg_re, Complex.one_re, neg_neg] using hz⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.mpr continuous_subtype_val
  continuous_invFun := continuous_induced_rng.mpr continuous_subtype_val

theorem ballHomeomorph_smul (g : BallNatural.BallGroup) (z : BallNatural.Ball) :
    ballHomeomorph (g • z) = BallGroupComparison.ballGroupComparison g • ballHomeomorph z := by
  apply Subtype.ext
  funext i
  change (BallNatural.asSL g).val.mulVec (DeterminantCoordinates.lineVector z.val) i.castSucc /
      (BallNatural.asSL g).val.mulVec (DeterminantCoordinates.lineVector z.val) 2 =
    Matrix.SpecialLinearGroup.toLin' (BallGroupComparison.ballGroupComparison g).val
      (Geometry.ComplexBall.ArithmeticQuotientBoostBall.liftVector z.val) i.castSucc /
    Matrix.SpecialLinearGroup.toLin' (BallGroupComparison.ballGroupComparison g).val
      (Geometry.ComplexBall.ArithmeticQuotientBoostBall.liftVector z.val) 2
  simp only [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  rfl

instance ballPretransitive : MulAction.IsPretransitive BallNatural.BallGroup BallNatural.Ball where
  exists_smul_eq x y := by
    let : MulAction.IsPretransitive (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (-1))
        (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (-1)) :=
      Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballAction_pretransitive (-1) (by norm_num) (by norm_num)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (-1)) (ballHomeomorph x) (ballHomeomorph y)
    refine ⟨BallGroupComparison.ballGroupComparison.symm g, ballHomeomorph.injective ?_⟩
    rw [ballHomeomorph_smul, BallGroupComparison.ballGroupComparison.apply_symm_apply]
    exact hg

instance ballProperSMul : ProperSMul BallNatural.BallGroup BallNatural.Ball where
  isProperMap_smul_pair := by
    let : ProperSMul (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (-1))
        (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (-1)) :=
      Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballAction_proper (-1) (by norm_num) (by norm_num)
    let e := BallGroupComparison.ballGroupComparison.toHomeomorph.prodCongr ballHomeomorph
    let f := ballHomeomorph.symm.prodCongr ballHomeomorph.symm
    have h := f.isProperMap.comp (ProperSMul.isProperMap_smul_pair.comp e.isProperMap)
    have he : f ∘ (fun p : Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) (-1) ×
        Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (-1) => (p.1 • p.2, p.2)) ∘ e =
        (fun p : BallNatural.BallGroup × BallNatural.Ball => (p.1 • p.2, p.2)) := by
      funext p
      apply Prod.ext
      · change ballHomeomorph.symm (BallGroupComparison.ballGroupComparison p.1 • ballHomeomorph p.2) = _
        rw [← ballHomeomorph_smul, ballHomeomorph.symm_apply_apply]
      · exact ballHomeomorph.symm_apply_apply p.2
    exact he ▸ h

theorem discrete_ball_properlyDiscontinuous (Γ : Subgroup BallNatural.BallGroup) [DiscreteTopology Γ] :
    ProperlyDiscontinuousSMul Γ BallNatural.Ball := by
  exact properlyDiscontinuousSMul_iff_properSMul.mpr inferInstance

end

end OAI.RepresentationTheory.Theta.Adelic.BallProper
