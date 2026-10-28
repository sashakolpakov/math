import OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator
import OAI.RepresentationTheory.Theta.Kernel.TopFixedLevelTransport

/-! # Linear Operator Fixed Level -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.LinearOperatorFixedLevel.IntrinsicMultiplier

/-! A commuting actual archimedean multiplier transports theta and top
forms at the original finite level. No equality of finite stabilizers is used. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.IntrinsicCommutingArch OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanIndependence.Intrinsic

variable (F : Type) [Field F] [NumberField F]

local instance (v : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance (v : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

variable {d : F} {m : ℕ}
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (hd : d ≠ 0) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

theorem theta_multiplier_weights
    (b : ∀ v : NumberField.InfinitePlace F, Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl v))
    (β : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) → ℂ)
    (hb : ∀ (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)),
      Adelic.ThetaEvaluation.archimedeanValue F (3 * m) (IntrinsicMultiplicityOperator.IntrinsicCommutingArch.archOperator F C b φ) x =
        β x * Adelic.ThetaEvaluation.archimedeanValue F (3 * m) φ x)
    (f f' : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (hw : ∀ x, Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f' (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      β x * Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x))
    (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) :
    Adelic.ThetaEvaluation.theta F (3 * m) (IntrinsicMultiplicityOperator.IntrinsicCommutingArch.archOperator F C b φ) f = Adelic.ThetaEvaluation.theta F (3 * m) φ f' := by
  apply tsum_congr
  intro x
  change Adelic.ThetaEvaluation.archimedeanValue F (3 * m) (IntrinsicMultiplicityOperator.IntrinsicCommutingArch.archOperator F C b φ) x *
      Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
    Adelic.ThetaEvaluation.archimedeanValue F (3 * m) φ x * Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f' (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)
  rw [hb,hw]
  ring

theorem finite_action_theta_of_commuting_operator
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (b : ∀ v : NumberField.InfinitePlace F, Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl v))
    (hb : ∀ v g, Commute (b v) (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) g))
    (f f' : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (ht : ∀ φ, Adelic.ThetaEvaluation.theta F (3 * m) (IntrinsicMultiplicityOperator.IntrinsicCommutingArch.archOperator F C b φ) f = Adelic.ThetaEvaluation.theta F (3 * m) φ f')
    (g : Adelic.SpecialUnitary.SU H.val) (hf : Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f = f)
    (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) :
    Adelic.ThetaEvaluation.theta F (3 * m) φ (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f') =
      Adelic.ThetaEvaluation.theta F (3 * m) φ f' := by
  let η := Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D (Adelic.RationalSU.rationalArchimedeanSU F H g)⁻¹ φ
  have hη : Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D (Adelic.RationalSU.rationalArchimedeanSU F H g) η = φ :=
    IntrinsicArchimedeanIndependence.Intrinsic.archimedeanAction_inv_cancel F H K hd P C D _ φ
  have he := Adelic.SpecialUnitaryTheta.rational_specialUnitary_theta F H K hd C P D hns hH hK g η f'
  rw [hη] at he
  have hc := IntrinsicMultiplicityOperator.IntrinsicCommutingArch.arch_operator_theta_fixed_level F H K hd P C D hns hH hK b hb g η f hf
  rw [hη,ht,ht] at hc
  exact he.trans hc.symm

theorem geometricTensor_of_theta_fixed
    {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)
    (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B) (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (hf : ∀ φ, Adelic.ThetaEvaluation.theta F (3 * m) φ (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f) =
      Adelic.ThetaEvaluation.theta F (3 * m) φ f) (a : ℕ) :
    Adelic.DataTheta.geometricTensor B (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f) a =
      Adelic.DataTheta.geometricTensor B f a := by
  have ht (z : Adelic.BallNatural.Ball) : Adelic.DataTheta.completedTheta B
      (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f) (B.period z).matrix =
        Adelic.DataTheta.completedTheta B f (B.period z).matrix := by
    funext ξ
    have he := hf (B.gaussian z ξ)
    rw [← hΘ.2.2.1,← hΘ.2.2.1] at he
    unfold Adelic.DataTheta.completedTheta
    rw [he]
  funext z
  unfold Adelic.DataTheta.geometricTensor Adelic.DataTheta.completedTensor
  rw [ht]

end RepresentationTheory.Theta.Kernel.LinearOperatorFixedLevel.IntrinsicMultiplier

namespace RepresentationTheory.Theta.Kernel.LinearOperatorFixedLevel.Intrinsic

/-! Fixed-level transport for compositions of actual Schwartz operators,
including native constructions presented with equal additive characters. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanIndependence.Intrinsic OAI.RepresentationTheory.Theta.Kernel.LinearOperatorFixedLevel.IntrinsicMultiplier

variable (F : Type) [Field F] [NumberField F]
variable {d : F} {m : ℕ}
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (hd : d ≠ 0) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

theorem linear_operator_theta_weights
    (L : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m) ≃ₗ[ℂ] Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m))
    (β : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) → ℂ)
    (hL : ∀ φ x, Adelic.ThetaEvaluation.archimedeanValue F (3 * m) (L φ) x = β x * Adelic.ThetaEvaluation.archimedeanValue F (3 * m) φ x)
    (f f' : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (hw : ∀ x, Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f' (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      β x * Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x))
    (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) :
    Adelic.ThetaEvaluation.theta F (3 * m) (L φ) f = Adelic.ThetaEvaluation.theta F (3 * m) φ f' := by
  apply tsum_congr
  intro x
  change Adelic.ThetaEvaluation.archimedeanValue F (3 * m) (L φ) x *
      Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
    Adelic.ThetaEvaluation.archimedeanValue F (3 * m) φ x * Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f' (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)
  rw [hL,hw]
  ring

theorem finite_action_theta_of_linear_operator
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (L : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m) ≃ₗ[ℂ] Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m))
    (hL : ∀ g φ, L (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g φ) =
      Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g (L φ))
    (f f' : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (ht : ∀ φ, Adelic.ThetaEvaluation.theta F (3 * m) (L φ) f = Adelic.ThetaEvaluation.theta F (3 * m) φ f')
    (g : Adelic.SpecialUnitary.SU H.val) (hf : Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f = f)
    (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) :
    Adelic.ThetaEvaluation.theta F (3 * m) φ (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f') =
      Adelic.ThetaEvaluation.theta F (3 * m) φ f' := by
  let η := Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D (Adelic.RationalSU.rationalArchimedeanSU F H g)⁻¹ φ
  have hη : Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D (Adelic.RationalSU.rationalArchimedeanSU F H g) η = φ :=
    IntrinsicArchimedeanIndependence.Intrinsic.archimedeanAction_inv_cancel F H K hd P C D _ φ
  have he := Adelic.SpecialUnitaryTheta.rational_specialUnitary_theta F H K hd C P D hns hH hK g η f'
  rw [hη] at he
  have hc := Adelic.SpecialUnitaryTheta.rational_specialUnitary_theta F H K hd C P D hns hH hK g (L η) f
  rw [hf,← hL,hη,ht,ht] at hc
  exact he.trans hc.symm

theorem theta_top_of_theta_fixed
    {K₂ : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K₂} (B : Adelic.DataTheta.ComparisonData F H K₂ A)
    (P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K₂) (C₂ : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2)
    (D₂ : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K₂ hd C₂ P₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B)
    (hCov : Adelic.DataTheta.Descent.RationalHeckeCovariance B P₂ hd C₂ D₂)
    (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hf : ∀ φ, Adelic.ThetaEvaluation.theta F 6 φ (Adelic.FiniteSchwartz.finiteAction F H K₂ hd C₂ P₂ D₂ (Adelic.RationalSU.rationalFiniteSU F H g) f) =
      Adelic.ThetaEvaluation.theta F 6 φ f) (z : Adelic.BallNatural.Ball) :
    (IntrinsicSecondProjection.Intrinsic.thetaTopForm B f (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
      (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
        (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) = IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z := by
  have ht := IntrinsicMultiplier.geometricTensor_of_theta_fixed F H K₂ hd P₂ C₂ D₂ B hΘ g f hf 2
  have he : IntrinsicSecondProjection.Intrinsic.thetaTopForm B (Adelic.FiniteSchwartz.finiteAction F H K₂ hd C₂ P₂ D₂ (Adelic.RationalSU.rationalFiniteSU F H g) f) =
      IntrinsicSecondProjection.Intrinsic.thetaTopForm B f := by
    funext w
    unfold IntrinsicSecondProjection.Intrinsic.thetaTopForm
    rw [ht]
  have hc := IntrinsicSecondAction.Intrinsic.thetaTopForm_covariance B P₂ hd C₂ D₂ hG hCov g f z
  rw [he] at hc
  exact hc

end RepresentationTheory.Theta.Kernel.LinearOperatorFixedLevel.Intrinsic

end

end OAI
