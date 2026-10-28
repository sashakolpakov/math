import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MixedTensor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Symmetry

/-! # One Sided Tor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OneSidedTor

noncomputable section

/-! If S is flat over R and N is an S-module flat over R, then
Tor over S of a base-changed R-module with N vanishes in positive degrees. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) [Module R N] [IsScalarTower R S N]

def derivedIso (n : ℕ) :
    ((Tor (ModuleCat S) n).obj N).obj ((ProjectionFormula.Flat.Extension.baseChange R S).obj M) ≅
      ((MixedTensor.tensor R S N).leftDerived n).obj M :=
  DerivedBaseChange.leftDerivedIso (MixedTensor.tensor R S N) (tensorLeft N)
    (ProjectionFormula.Flat.Extension.baseChange R S) (𝟭 _) (MixedTensor.cancelBaseChange R S N) M n

theorem higher_isZero [Module.Flat R N] (n : ℕ) :
    IsZero (((Tor (ModuleCat S) (n + 1)).obj
      ((ProjectionFormula.Flat.Extension.baseChange R S).obj M)).obj N) := by
  apply IsZero.of_iso _ (ProjectionFormula.Tor.Symmetry.iso S _ N (n + 1))
  exact IsZero.of_iso (MixedTensor.higherDerived_isZero R S N M n)
    (derivedIso R S M N (n + 1))

theorem higher_length [Module.Flat R N] (n : ℕ) :
    Module.length S (((Tor (ModuleCat S) (n + 1)).obj
      ((ProjectionFormula.Flat.Extension.baseChange R S).obj M)).obj N) = 0 := by
  let := ModuleCat.subsingleton_of_isZero (higher_isZero R S M N n)
  exact Module.length_eq_zero

def zeroEquiv :
    (((Tor (ModuleCat S) 0).obj ((ProjectionFormula.Flat.Extension.baseChange R S).obj M)).obj N) ≃ₗ[S]
      N ⊗[R] M :=
  (ProjectionFormula.Tor.Flat.torZeroIso S _ N).toLinearEquiv.trans
    ((TensorProduct.comm S _ N).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N M))

theorem euler_length [Module.Flat R N] (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length S (((Tor (ModuleCat S) i).obj
        ((ProjectionFormula.Flat.Extension.baseChange R S).obj M)).obj N)).toNat) =
      (Module.length S (N ⊗[R] M)).toNat := by
  rw [Finset.sum_range_succ']
  simp [higher_length, (zeroEquiv R S M N).length_eq]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OneSidedTor
