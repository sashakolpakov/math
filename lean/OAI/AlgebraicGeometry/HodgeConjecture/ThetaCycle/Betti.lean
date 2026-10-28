import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm
import OAI.AlgebraicTopology.Kunneth.CupPullbackSingular

/-! # Betti -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Betti.CM

noncomputable section

/-! Pullback and nonvanishing transport for the actual four embedding classes. -/

open _root_.CategoryTheory

theorem betti_pullback_comp {X Y Z : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (g : Y.toOver ⟶ Z.toOver) (n : ℕ)
    (z : Z.complexCohomology n) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n (f ≫ g) z =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n g z) :=
  ConcreteCategory.congr_hom
    ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℂ ℂ) n).map_comp g.op f.op) z

theorem cup_pullback {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (a : Y.complexCohomology p) (b : Y.complexCohomology q) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + q) f (Cm.cup Y p q a b) =
      Cm.cup X p q (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) p f a)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) q f b) :=
  AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) p q a b

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
  (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)))

theorem fourClass_pullback {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (p : Y.toOver ⟶ X.toOver)
    (f : (i : Fin 4) → X.toOver ⟶ (R i).abelianVariety.toOver) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 4 p (Cm.fourClass K v R X f) =
      Cm.fourClass K v R Y (fun i => p ≫ f i) := by
  dsimp only [Cm.fourClass]
  rw [cup_pullback p 2 2, cup_pullback p 1 1, cup_pullback p 1 1]
  simp only [betti_pullback_comp]

theorem fourClass_evaluate_pullback
    {B : HeckeCycles.GeometricSource.CM.BallDatum K} {N M : ℕ}
    {S : Cm.PrincipalBallSurface K B N} {T : Cm.PrincipalBallSurface K B M}
    (p : Cm.PrincipalRefinement K S T)
    (f : (i : Fin 4) → S.surface.variety.toOver ⟶ (R i).abelianVariety.toOver) :
    T.surface.evaluate (Cm.fourClass K v R T.surface.variety (fun i => p.map ≫ f i)) =
      (p.degree : ℂ) * S.surface.evaluate (Cm.fourClass K v R S.surface.variety f) := by
  rw [← fourClass_pullback K v R p.map f, p.evaluate_pullback]

theorem fourClass_evaluate_pullback_ne_zero
    {B : HeckeCycles.GeometricSource.CM.BallDatum K} {N M : ℕ}
    {S : Cm.PrincipalBallSurface K B N} {T : Cm.PrincipalBallSurface K B M}
    (p : Cm.PrincipalRefinement K S T)
    (f : (i : Fin 4) → S.surface.variety.toOver ⟶ (R i).abelianVariety.toOver)
    (hf : S.surface.evaluate (Cm.fourClass K v R S.surface.variety f) ≠ 0) :
    T.surface.evaluate
      (Cm.fourClass K v R T.surface.variety (fun i => p.map ≫ f i)) ≠ 0 := by
  rw [← fourClass_pullback K v R p.map f]
  exact p.evaluate_pullback_ne_zero _ hf

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Betti.CM
