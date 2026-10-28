import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConeProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CupNaturality

/-! # Cochain Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CochainCup

noncomputable section

/-! The native crystalline coefficient lift carries the original
cochain product rule and actual categorical cohomology cup. -/

open _root_.CategoryTheory

universe u
variable (B : Type u) [CommRing B] (K : CochainComplex (ModuleCat.{u} B) ℕ)
  (μ : ∀ i j, K.X i →ₗ[B] K.X j →ₗ[B] K.X (i+j))
  (hμ : ∀ i j (x : K.X i) (y : K.X j),
    K.d (i+j) (i+j+1) (μ i j x y) =
      Cochain.CohomologyCup.cupInto K μ (i+1) j (i+j+1) (by omega)
        (K.d i (i+1) x) y +
      (-1 : ℤ)^i • Cochain.CohomologyCup.cupInto K μ i (j+1) (i+j+1) (by omega)
        x (K.d j (j+1) y))

local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConeProduct.coefficientSource B K
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConeProduct.sourcePairing B K μ

private theorem cast_down {i j : ℕ} (h : i=j) (x : (L).X i) :
    (Cochain.CohomologyCup.degreeCast L h x).down =
      Cochain.CohomologyCup.degreeCast K h x.down := by
  subst j
  rfl

include hμ in
theorem differential (i j : ℕ) (x : (L).X i) (y : (L).X j) :
    (L).d (i+j) (i+j+1) (ν i j x y) =
      Cochain.CohomologyCup.cupInto L ν (i+1) j (i+j+1) (by omega)
        ((L).d i (i+1) x) y +
      (-1 : ℤ)^i • Cochain.CohomologyCup.cupInto L ν i (j+1) (i+j+1) (by omega)
        x ((L).d j (j+1) y) := by
  apply ULift.ext
  change K.d (i+j) (i+j+1) (μ i j x.down y.down) =
    (Cochain.CohomologyCup.degreeCast L (by omega : (i+1)+j=i+j+1)
      (ν (i+1) j ((L).d i (i+1) x) y)).down +
    (-1 : ℤ)^i • (Cochain.CohomologyCup.degreeCast L (by omega : i+(j+1)=i+j+1)
      (ν i (j+1) x ((L).d j (j+1) y))).down
  exact (hμ i j x.down y.down).trans
    (congrArg₂ (fun x y => x + (-1 : ℤ)^i • y)
      (cast_down B K (by omega : (i+1)+j=i+j+1) _).symm
      (cast_down B K (by omega : i+(j+1)=i+j+1) _).symm)

abbrev cup := Cochain.CohomologyCup.cohomologyCup L ν (differential B K μ hμ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CochainCup
