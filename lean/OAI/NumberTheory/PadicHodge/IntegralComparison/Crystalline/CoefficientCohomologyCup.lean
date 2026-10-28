import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CochainCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.CochainCup

/-! # Coefficient Cohomology Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientCohomologyCup

noncomputable section

/-! The original crystalline coefficient lift preserves the actual
cohomology cup under its canonical homology isomorphism. -/

open _root_.CategoryTheory

universe u
variable (B : Type u) [CommRing B]
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := B)

local instance additive : (F).Additive where
  map_add := by intros; rfl

def coefficient (M : ModuleCat.{u} B) : M →+ (F).obj M where
  toFun := ULift.up
  map_zero' := rfl
  map_add' _ _ := rfl

theorem natural {M N : ModuleCat.{u} B} (f : M ⟶ N) (x : M) :
    (F).map f (coefficient B M x) = coefficient B N (f x) := rfl

variable (K : CochainComplex (ModuleCat.{u} B) ℕ)
  (μ : ∀ i j, K.X i →ₗ[B] K.X j →ₗ[B] K.X (i+j))
  (hμ : ∀ i j (x : K.X i) (y : K.X j),
    K.d (i+j) (i+j+1) (μ i j x y) =
      Cochain.CohomologyCup.cupInto K μ (i+1) j (i+j+1) (by omega)
        (K.d i (i+1) x) y +
      (-1 : ℤ)^i • Cochain.CohomologyCup.cupInto K μ i (j+1) (i+j+1) (by omega)
        x (K.d j (j+1) y))

def map (i : ℕ) := Mapped.CochainCup.map F (coefficient B) K i

theorem map_apply (i : ℕ) (x : K.homology i) :
    CoefficientCohomologyCup.map B K i x =
      (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso F K i).inv (ULift.up x) := rfl

theorem map_bijective (i : ℕ) : Function.Bijective (CoefficientCohomologyCup.map B K i) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso F K i).symm.toLinearEquiv.bijective.comp
    ⟨ULift.up_injective, fun x => ⟨x.down, rfl⟩⟩

abbrev map_cup := Mapped.CochainCup.map_cup F (coefficient B) (natural B) K μ
  (ConeProduct.sourcePairing B K μ) hμ
  (CochainCup.differential B K μ hμ) (fun _ _ _ _ => rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientCohomologyCup
