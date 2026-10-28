import OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData

/-! # Intrinsic Archimedean Independence -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanIndependence.Intrinsic

noncomputable section

/-! The full AdelicTheta uniqueness conclusion identifies the archimedean SU
operators for any two native constructions with the same additive
character and rational frames. Their finite actions consequently give
the same theta evaluations, without choosing new finite stabilizers. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData

variable (F : Type) [Field F] [NumberField F]

local instance (v : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance (v : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

theorem operator_eq_of_unique {N : ℕ} (v : NumberField.InfinitePlace F)
    {G : Type} [Group G] [TopologicalSpace G]
    (ψ ψ' : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hψ : ψ' = ψ)
    (r : G → Weil.Local.FunctionsMetaplectic.Construction.Symplectic (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) N)
    (s : G →ₜ* Weil.AdelicSplitting.Vacuum.Construction.CoverAt F N ψ (.inl v))
    (s' : G →ₜ* Weil.AdelicSplitting.Vacuum.Construction.CoverAt F N ψ' (.inl v))
    (hs' : ∀ g, Weil.AdelicSplitting.Vacuum.Construction.projectionAt F N ψ' (.inl v) (s' g) = r g)
    (hu : ∀ t : G →ₜ* Weil.AdelicSplitting.Vacuum.Construction.CoverAt F N ψ (.inl v),
      (∀ g, Weil.AdelicSplitting.Vacuum.Construction.projectionAt F N ψ (.inl v) (t g) = r g) → ∀ g, t g = s g)
    (g : G) :
    Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ' (.inl v)) (s' g) =
      Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) N (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl v)) (s g) := by
  subst ψ'
  rw [hu s' hs' g]

variable {d : F} {m : ℕ}
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (hd : d ≠ 0) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
variable (C C' : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)
variable (D' : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C' P)

theorem archimedeanAction_independent (hψ : C'.ψ = C.ψ)
    (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) :
    Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C' P D' g φ = Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g φ := by
  funext v
  apply congrArg (fun L => L (φ v))
    (operator_eq_of_unique F v C.ψ C'.ψ hψ
      (fun a => Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 m H K P (.inl v) (Adelic.FiniteSchwartz.localSUToPair F H K (.inl v) a))
      (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v))
      (Adelic.FiniteSchwartz.localSUSplitting F H K hd C' P D' (.inl v))
      (fun a => D'.covers (.inl v) (Adelic.FiniteSchwartz.localSUToPair F H K (.inl v) a)) (hu v) (g v))

theorem archimedeanAction_inv_cancel (g : Adelic.RationalSU.ArchimedeanSU F H)
    (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) :
    Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g
      (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g⁻¹ φ) = φ := by
  funext v
  change ((Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _).comp (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v)).toMonoidHom)
    (g v) (((Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _).comp
      (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v)).toMonoidHom) ((g v)⁻¹) (φ v)) = φ v
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem finite_action_theta_independent
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val)
    (hK : K.val.conjTranspose = -K.val)
    (hψ : C'.ψ = C.ψ) (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D)
    (g : Adelic.SpecialUnitary.SU H.val) (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) :
    Adelic.ThetaEvaluation.theta F (3 * m) φ (Adelic.FiniteSchwartz.finiteAction F H K hd C' P D' (Adelic.RationalSU.rationalFiniteSU F H g) f) =
      Adelic.ThetaEvaluation.theta F (3 * m) φ (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f) := by
  let η := Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D (Adelic.RationalSU.rationalArchimedeanSU F H g)⁻¹ φ
  have h₁ := Adelic.SpecialUnitaryTheta.rational_specialUnitary_theta F H K hd C P D hns hH hK g η f
  have h₂ := Adelic.SpecialUnitaryTheta.rational_specialUnitary_theta F H K hd C' P D' hns hH hK g η f
  rw [archimedeanAction_independent F H K hd P C C' D D' hψ hu] at h₂
  have hη : Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D (Adelic.RationalSU.rationalArchimedeanSU F H g) η = φ :=
    archimedeanAction_inv_cancel F H K hd P C D _ φ
  rw [hη] at h₁ h₂
  exact h₂.trans h₁.symm

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanIndependence.Intrinsic
