import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalFiniteEquiv
import OAI.RepresentationTheory.Theta.Kernel.Definitions
import OAI.RepresentationTheory.Theta.Adelic.CompactSupport

/-! # Rational Schwartz Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalSchwartzCoordinates.CM

noncomputable section

/-! ThetaCycle: transport actual finite Schwartz functions between the two
rational adelic models, preserving every rational theta coefficient. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

def finiteSchwartzHomeomorphEquiv {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.FiniteSchwartz Y ≃ RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.FiniteSchwartz X where
  toFun f := ⟨f.val ∘ h, f.property.1.comp_continuous h.continuous,
    f.property.2.comp_homeomorph h⟩
  invFun f := ⟨f.val ∘ h.symm, f.property.1.comp_continuous h.symm.continuous,
    f.property.2.comp_homeomorph h.symm⟩
  left_inv f := by
    apply Subtype.ext
    funext y
    exact congrArg f.val (h.apply_symm_apply y)
  right_inv f := by
    apply Subtype.ext
    funext x
    exact congrArg f.val (h.symm_apply_apply x)

theorem finite_schwartz_homeomorph_equiv_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y)
    (f : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.FiniteSchwartz Y) (x : X) :
    (finiteSchwartzHomeomorphEquiv h f).val x = f.val (h x) := rfl

def rationalFinitePositionHomeomorph (I : Type*) :
    (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) ≃ₜ (I → RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.AQf) :=
  Homeomorph.piCongrRight (fun _ : I => RationalFiniteEquiv.CM.rationalFiniteAdeleHomeomorph)

theorem rational_finite_position_homeomorph_principal {I : Type*} (x : I → ℚ) :
    rationalFinitePositionHomeomorph I (fun i => algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) (x i)) =
      fun i => algebraMap ℚ RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.AQf (x i) := by
  funext i
  exact RationalFiniteCoordinates.CM.rational_finite_adele_map_principal (x i)

def rationalSchwartzInputEquiv (I : Type*) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I ≃ RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.FiniteSchwartz (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) :=
  finiteSchwartzHomeomorphEquiv (rationalFinitePositionHomeomorph I)

theorem rational_schwartz_input_principal {I : Type*} (f : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) (x : I → ℚ) :
    (rationalSchwartzInputEquiv I f).val (fun i => algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) (x i)) =
      f.val (fun i => algebraMap ℚ RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.AQf (x i)) := by
  change f.val (rationalFinitePositionHomeomorph I _) = _
  rw [rational_finite_position_homeomorph_principal]

def rationalSchwartzToAdelicFunctions (N : ℕ) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N) ≃ RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions ℚ N :=
  rationalSchwartzInputEquiv (Fin N)

theorem rational_schwartz_to_adelic_principal (N : ℕ) (f : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) (x : Fin N → ℚ) :
    (rationalSchwartzToAdelicFunctions N f).val
        (fun i => algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) (x i)) =
      f.val (fun i => algebraMap ℚ RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.AQf (x i)) :=
  rational_schwartz_input_principal f x

theorem rational_schwartz_theta_series {I : Type*} [Fintype I]
    (f : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) (B : Matrix I I ℂ) (z : I → ℂ) :
    (∑' x : I → ℚ, (rationalSchwartzInputEquiv I f).val
        (fun i => algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) (x i)) * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel B x z) = RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta f B z := by
  apply tsum_congr
  intro x
  rw [rational_schwartz_input_principal]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalSchwartzCoordinates.CM
