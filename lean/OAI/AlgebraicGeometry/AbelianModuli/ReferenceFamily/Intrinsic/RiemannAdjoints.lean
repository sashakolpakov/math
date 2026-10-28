import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodBilinearExt
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodAdjoints

/-! # Riemann Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual native complex-linear PEL endomorphisms are adjoint for
the positive Hermitian form constructed from the ample polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem Intrinsic.RiemannAdjoints.nativeChernForm_real (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (v w : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    TypeElevenBilinear.realCovectorBilinear (AmpleChernInvariant.nativeChernCovector A L) v.val w.val = (Intrinsic.ChernPairing.nativeChernForm A L v w : ℝ) :=
  (TypeElevenBilinear.realCovectorBilinear_apply (AmpleChernInvariant.nativeChernCovector A L) v.val w.val).trans
    ((congrArg Complex.re (Intrinsic.ChernPeriod.nativeChernForm_covector A L v w)).trans (Complex.ratCast_re _))

theorem Intrinsic.RiemannAdjoints.realChernForm_lift_adjoint (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (f g : A.toOver ⟶ A.toOver) [IsMonHom f] [IsMonHom g]
    (hfg : ∀ x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A,
      Intrinsic.ChernPairing.nativeChernForm A L (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) y = Intrinsic.ChernPairing.nativeChernForm A L x (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift g y))
    (u v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    TypeElevenBilinear.realCovectorBilinear (AmpleChernInvariant.nativeChernCovector A L) (Intrinsic.Maps.IntrinsicLinearMaps.linearLift f u) v =
      TypeElevenBilinear.realCovectorBilinear (AmpleChernInvariant.nativeChernCovector A L) u (Intrinsic.Maps.IntrinsicLinearMaps.linearLift g v) := by
  let B := TypeElevenBilinear.realCovectorBilinear (AmpleChernInvariant.nativeChernCovector A L)
  have he : B.compl₁₂ ((Intrinsic.Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℝ) LinearMap.id =
      B.compl₁₂ LinearMap.id ((Intrinsic.Maps.IntrinsicLinearMaps.linearLift g).restrictScalars ℝ) := by
    apply Real.PeriodBilinearExt.realPeriodBilinear_ext A
    intro x y
    exact (Intrinsic.RiemannAdjoints.nativeChernForm_real A L (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) y).trans
      ((congrArg (fun q : ℚ => (q : ℝ)) (hfg x y)).trans
        (Intrinsic.RiemannAdjoints.nativeChernForm_real A L x (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift g y)).symm)
  exact congrArg (fun b => b u v) he

theorem Intrinsic.RiemannAdjoints.nativeRiemannForm_lift_adjoint (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)
    (f g : A.toOver ⟶ A.toOver) [IsMonHom f] [IsMonHom g]
    (hfg : ∀ x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A,
      Intrinsic.ChernPairing.nativeChernForm A L (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) y = Intrinsic.ChernPairing.nativeChernForm A L x (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift g y))
    (u v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    Intrinsic.RiemannForm.nativeRiemannForm A L hL (Intrinsic.Maps.IntrinsicLinearMaps.linearLift f u) v = Intrinsic.RiemannForm.nativeRiemannForm A L hL u (Intrinsic.Maps.IntrinsicLinearMaps.linearLift g v) := by
  apply Complex.ext
  · change TypeElevenBilinear.realCovectorBilinear (AmpleChernInvariant.nativeChernCovector A L) (Intrinsic.Maps.IntrinsicLinearMaps.linearLift f u) (Complex.I • v) =
      TypeElevenBilinear.realCovectorBilinear (AmpleChernInvariant.nativeChernCovector A L) u (Complex.I • Intrinsic.Maps.IntrinsicLinearMaps.linearLift g v)
    exact (Intrinsic.RiemannAdjoints.realChernForm_lift_adjoint A L f g hfg u (Complex.I • v)).trans
      (congrArg (TypeElevenBilinear.realCovectorBilinear (AmpleChernInvariant.nativeChernCovector A L) u) ((Intrinsic.Maps.IntrinsicLinearMaps.linearLift g).map_smul Complex.I v))
  · exact Intrinsic.RiemannAdjoints.realChernForm_lift_adjoint A L f g hfg u v

theorem ActionData.RosatiConjugation.native_riemann_adjoint
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : ActionData.RosatiConjugation A ρ) (a : NumberField.RingOfIntegers E) :
    let P := Polarized.Projectivity.polarizedNativeProjectivePresentation A
    let H := Intrinsic.RiemannForm.nativeRiemannForm (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian P) (Intrinsic.ChernPairing.polarizationLineBundle A) (Intrinsic.ChernPairing.polarizationLineBundle_ample A)
    ∀ u v, H (Intrinsic.Maps.IntrinsicLinearMaps.linearLift (Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A.abelian P
        (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))) u) v =
      H u (Intrinsic.Maps.IntrinsicLinearMaps.linearLift (Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A.abelian P (ρ.map a)) v) := by
  intro P H u v
  exact Intrinsic.RiemannAdjoints.nativeRiemannForm_lift_adjoint (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian P) (Intrinsic.ChernPairing.polarizationLineBundle A)
    (Intrinsic.ChernPairing.polarizationLineBundle_ample A) _ _ (ActionData.RosatiConjugation.period_adjoint A ρ hρ a) u v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
