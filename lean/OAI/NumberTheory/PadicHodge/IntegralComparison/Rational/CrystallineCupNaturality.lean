import OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CrystallineCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CrystallineCupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearScalarExtension

/-! # Crystalline Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CrystallineCupNaturality

noncomputable section

/-! Actual geometric pullback preserves the native rational crystalline
cup, by scalar extension of the proved integral identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

private def restrict {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S M] [Module S N]
    (φ : S →+* R) (hM : ∀ s (x : M), s • x = φ s • x)
    (hN : ∀ s (x : N), s • x = φ s • x) (b : M →ₗ[R] N) : M →ₗ[S] N where
  toFun := b
  map_add' := b.map_add
  map_smul' s x := by
    rw [hM, hN]
    exact b.map_smul (φ s) x

private theorem tensor_natural {A S M N M' N' P P' : Type*}
    [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup M'] [Module S M'] [AddCommGroup N'] [Module S N']
    [AddCommGroup P] [Module S P] [AddCommGroup P'] [Module S P']
    (μ : S ⊗[A] M →ₗ[S] S ⊗[A] N →ₗ[S] P)
    (ν : M' →ₗ[S] N' →ₗ[S] P')
    (f : S ⊗[A] M →ₗ[S] M') (g : S ⊗[A] N →ₗ[S] N') (h : P →ₗ[S] P')
    (H : ∀ a b x y, h (μ (a ⊗ₜ[A] x) (b ⊗ₜ[A] y)) =
      ν (f (a ⊗ₜ[A] x)) (g (b ⊗ₜ[A] y)))
    (x : S ⊗[A] M) (y : S ⊗[A] N) : h (μ x y) = ν (f x) (g y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul b y => exact H a b x y

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  [IsProper Y.hom] [Smooth Y.hom] (g : X ⟶ Y)

local notation "W" => WittVector p k
local notation "K" => FractionRing (WittVector p k)
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

def integralPullback (i : ℕ) : Witt.Crystalline.integralCohomology p k Y i →ₗ[W] Witt.Crystalline.integralCohomology p k X i :=
  restrict (ULift.ringEquiv : R ≃+* W).symm.toRingHom (fun _ _ => rfl) (fun _ _ => rfl)
    (Integral.CrystallineCupNaturality.pullback p k X Y g i)

def pullback (i : ℕ) : Witt.Crystalline.rationalCohomology p k Y i →ₗ[K] Witt.Crystalline.rationalCohomology p k X i :=
  (integralPullback p k X Y g i).baseChange K

variable (hX : Projectivity.Construction.ProjectiveOver k X.hom) (hY : Projectivity.Construction.ProjectiveOver k Y.hom)

omit [Fintype k] [Smooth X.hom] [Smooth Y.hom] in
theorem integralPullback_apply (i : ℕ) (x : Witt.Crystalline.integralCohomology p k Y i) :
    integralPullback p k X Y g i x = Integral.CrystallineCupNaturality.pullback p k X Y g i x := rfl

private theorem integralCup_apply
    (Z : Over (Spec (CommRingCat.of k))) [IsProper Z.hom] [Smooth Z.hom]
    (hZ : Projectivity.Construction.ProjectiveOver k Z.hom) (i j : ℕ)
    (x : Witt.Crystalline.integralCohomology p k Z i) (y : Witt.Crystalline.integralCohomology p k Z j) :
    CrystallineCup.integralCup p k Z hZ i j x y =
      Integral.CrystallineCup.cup p k Z hZ i j x y := rfl

omit [Fintype k] [Smooth X.hom] [Smooth Y.hom] in
theorem pullback_tmul (i : ℕ) (a : K) (x : Witt.Crystalline.integralCohomology p k Y i) :
    pullback p k X Y g i (a ⊗ₜ[W] x) = a ⊗ₜ[W] integralPullback p k X Y g i x :=
  LinearMap.baseChange_tmul (integralPullback p k X Y g i) a x

theorem integral_cup_natural (i j : ℕ) (x : Witt.Crystalline.integralCohomology p k Y i) (y : Witt.Crystalline.integralCohomology p k Y j) :
    integralPullback p k X Y g (i + j) (CrystallineCup.integralCup p k Y hY i j x y) =
      CrystallineCup.integralCup p k X hX i j
        (integralPullback p k X Y g i x) (integralPullback p k X Y g j y) := by
  rw [integralCup_apply, integralCup_apply, integralPullback_apply,
    integralPullback_apply, integralPullback_apply]
  exact Integral.CrystallineCupNaturality.cup_natural p k X Y g hX hY i j x y

theorem cup_natural (i j : ℕ) (x : Witt.Crystalline.rationalCohomology p k Y i) (y : Witt.Crystalline.rationalCohomology p k Y j) :
    pullback p k X Y g (i + j) (CrystallineCup.cup p k Y hY i j x y) =
      CrystallineCup.cup p k X hX i j (pullback p k X Y g i x) (pullback p k X Y g j y) := by
  apply tensor_natural
    (CrystallineCup.cup p k Y hY i j)
    (CrystallineCup.cup p k X hX i j)
    (pullback p k X Y g i) (pullback p k X Y g j) (pullback p k X Y g (i + j))
    (fun a b x y => ?_) x y
  have Hi : integralPullback p k X Y g (i + j)
        (Integral.CrystallineCup.cup p k Y hY i j x y) =
      Integral.CrystallineCup.cup p k X hX i j
        (integralPullback p k X Y g i x) (integralPullback p k X Y g j y) := by
    rw [integralPullback_apply, integralPullback_apply, integralPullback_apply]
    exact Integral.CrystallineCupNaturality.cup_natural p k X Y g hX hY i j x y
  exact (congrArg (pullback p k X Y g (i + j))
    (CrystallineCup.cup_tmul p k Y hY i j a b x y)).trans
    ((pullback_tmul p k X Y g (i + j) (a * b)
      (Integral.CrystallineCup.cup p k Y hY i j x y)).trans
      ((congrArg (fun z => (a * b) ⊗ₜ[W] z) Hi).trans
        ((CrystallineCup.cup_tmul p k X hX i j a b
          (integralPullback p k X Y g i x) (integralPullback p k X Y g j y)).symm.trans
          (congrArg₂ (fun x' y' => CrystallineCup.cup p k X hX i j x' y')
            (pullback_tmul p k X Y g i a x).symm
            (pullback_tmul p k X Y g j b y).symm))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CrystallineCupNaturality
