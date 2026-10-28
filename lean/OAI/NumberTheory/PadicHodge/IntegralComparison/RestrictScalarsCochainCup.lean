import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.CochainCup
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Restrict Scalars Cochain Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictScalarsCochainCup

noncomputable section

/-! Scalar restriction preserves the actual cochain product and its
canonical categorical cohomology product. -/

open _root_.CategoryTheory

universe u v w
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (K : CochainComplex (ModuleCat.{w} S) ℕ)

local notation "F" => ModuleCat.restrictScalars (algebraMap R S)
local notation "L" => Functor.obj (Functor.mapHomologicalComplex F (ComplexShape.up ℕ)) K
local instance restrictedModule (V : ModuleCat.{w} S) : Module R V :=
  Module.compHom V (algebraMap R S)
local instance tower (V : ModuleCat.{w} S) : IsScalarTower R S V where
  smul_assoc r s x := by rw [Algebra.smul_def]; exact mul_smul _ _ _

variable (μ : ∀ i j, K.X i →ₗ[S] K.X j →ₗ[S] K.X (i+j))

def pairing (i j : ℕ) : (L).X i →ₗ[R] (L).X j →ₗ[R] (L).X (i+j) :=
  (μ i j).restrictScalars₁₂ R R

private theorem cast_eq {i j : ℕ} (h : i=j) (x : K.X i) :
    Cochain.CohomologyCup.degreeCast L h x = Cochain.CohomologyCup.degreeCast K h x := by subst j; rfl

variable (hμ : ∀ i j (x : K.X i) (y : K.X j),
  K.d (i+j) (i+j+1) (μ i j x y) =
    Cochain.CohomologyCup.cupInto K μ (i+1) j (i+j+1) (by omega) (K.d i (i+1) x) y +
    (-1 : ℤ)^i • Cochain.CohomologyCup.cupInto K μ i (j+1) (i+j+1) (by omega) x (K.d j (j+1) y))

include hμ in
theorem differential (i j : ℕ) (x : (L).X i) (y : (L).X j) :
    (L).d (i+j) (i+j+1) (pairing R S K μ i j x y) =
      Cochain.CohomologyCup.cupInto L (pairing R S K μ) (i+1) j (i+j+1) (by omega) ((L).d i (i+1) x) y +
      (-1 : ℤ)^i • Cochain.CohomologyCup.cupInto L (pairing R S K μ) i (j+1) (i+j+1) (by omega) x ((L).d j (j+1) y) := by
  change K.d (i+j) (i+j+1) (μ i j x y) =
    Cochain.CohomologyCup.degreeCast L (by omega : (i+1)+j=i+j+1) (μ (i+1) j (K.d i (i+1) x) y) +
    (-1 : ℤ)^i • Cochain.CohomologyCup.degreeCast L (by omega : i+(j+1)=i+j+1) (μ i (j+1) x (K.d j (j+1) y))
  rw [cast_eq, cast_eq]
  exact hμ i j x y

def map (i : ℕ) := Mapped.CochainCup.map F (fun M => AddMonoidHom.id M) K i

abbrev map_cup := Mapped.CochainCup.map_cup F (fun M => AddMonoidHom.id M)
  (fun _ _ => rfl) K μ (pairing R S K μ) hμ (differential R S K μ hμ)
  (fun _ _ _ _ => rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictScalarsCochainCup
