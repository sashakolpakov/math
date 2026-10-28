import OAI.RepresentationTheory.Theta.Adelic.GeometricFrameCocycle
import OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
import OAI.RepresentationTheory.Theta.Adelic.CovariantOrbit
import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Tensor Orbit Setoid -/

namespace OAI.RepresentationTheory.Theta.Adelic.TensorOrbitSetoid

noncomputable section

/-! The tensor-bundle orbit relation in the statement is an equivalence
relation for every actual principal level which is a subgroup. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.GeometricGroup OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.GeometricFrameCocycle OAI.RepresentationTheory.Theta.Adelic.CovariantOrbit

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def rationalBallHom : SpecialUnitary.SU H.val →* BallNatural.BallGroup :=
  (GeometricGroup.geometricBallHom A).toMonoidHom.comp (RationalSU.rationalArchimedeanSU F H)

@[instance_reducible] def rationalBallAction : MulAction (SpecialUnitary.SU H.val) BallNatural.Ball :=
  MulAction.compHom BallNatural.Ball (rationalBallHom A)

theorem tensorOrbit_equivalence (N a : ℕ) (Γ : Subgroup (SpecialUnitary.SU H.val))
    (hΓ : ∀ g, g ∈ Γ ↔ BallGeometryData.PrincipalLevel N g) :
    Equivalence (DataTheta.Descent.TensorOrbit (GeometricGaussians.constructedComparison A P) N a) := by
  let := rationalBallAction A
  let u : SpecialUnitary.SU H.val → BallNatural.Ball → (Fin a → BallGeometryData.FrameIndex A → ℂ) → (Fin a → BallGeometryData.FrameIndex A → ℂ) :=
    fun g z v i => BallGeometryData.dualFrameChange A (RationalSU.rationalArchimedeanSU F H g) z (v i)
  let c : SpecialUnitary.SU H.val → BallNatural.Ball → ℂ := fun g z => BallNatural.Factors.naturalHalfFactor m (rationalBallHom A g) z
  have hu1 : ∀ z v, u 1 z v = v := by
    intro z v
    funext i
    simp only [u, map_one, GeometricFrameCocycle.dualFrameChange_one]
  have hum : ∀ g h z v, u (g * h) z v = u g (h • z) (u h z v) := by
    intro g h z v
    funext i
    change BallGeometryData.dualFrameChange A (RationalSU.rationalArchimedeanSU F H (g * h)) z (v i) = _
    rw [map_mul, GeometricFrameCocycle.dualFrameChange_mul]
    rfl
  have hc1 : ∀ z, c 1 z = 1 := by
    intro z
    simp [c, BallNatural.Factors.naturalHalfFactor]
  have hcm : ∀ g h z, c (g * h) z = c g (h • z) * c h z := by
    intro g h z
    dsimp only [c]
    rw [map_mul, BallNatural.Factors.naturalHalfFactor_mul]
    rfl
  have he := CovariantOrbit.covariantOrbit_equivalence Γ
    (fun T : DataTheta.Descent.SymmetricTensor (A := A) a => fun v => T.val v) u c hu1 hum hc1 hcm
  have hr : CovariantOrbit.covariantOrbit Γ (fun T : DataTheta.Descent.SymmetricTensor (A := A) a => fun v => T.val v) u c =
      DataTheta.Descent.TensorOrbit (GeometricGaussians.constructedComparison A P) N a := by
    funext p q
    apply propext
    simp only [CovariantOrbit.covariantOrbit, DataTheta.Descent.TensorOrbit, ← hΓ]
    rfl
  rw [hr] at he
  exact he

def tensorOrbitSetoid (N a : ℕ) (Γ : Subgroup (SpecialUnitary.SU H.val))
    (hΓ : ∀ g, g ∈ Γ ↔ BallGeometryData.PrincipalLevel N g) :
    Setoid (BallNatural.Ball × DataTheta.Descent.SymmetricTensor (A := A) a) where
  r := DataTheta.Descent.TensorOrbit (GeometricGaussians.constructedComparison A P) N a
  iseqv := tensorOrbit_equivalence A P N a Γ hΓ

end

end OAI.RepresentationTheory.Theta.Adelic.TensorOrbitSetoid
