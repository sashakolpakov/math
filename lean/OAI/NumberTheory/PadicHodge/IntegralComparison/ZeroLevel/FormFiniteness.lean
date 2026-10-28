import OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialFormFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame

/-! # Form Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.FormFiniteness

noncomputable section

/-!
# IntegralComparison: the actual Witt-relative forms of a zeroth-level chart are finite
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k C : Type u) [Field k] [CommRing C] [Algebra k C]

local notation "W" => WittVector p k

local instance residueAlgebra : Algebra W k := WittVector.constantCoeff.toAlgebra

local instance ambientAlgebra : Algebra W C :=
  ((algebraMap k C).comp WittVector.constantCoeff).toAlgebra

local instance coefficientTower : IsScalarTower W k C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def formsEquiv (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W C ⊥ (dividedPowersBot C) n ≃ₗ[C] AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form k C ⊥ (dividedPowersBot C) n :=
  PD.FormsBaseQuotient.formsEquiv W k C (WittVector.constantCoeff_surjective p) ⊥ (dividedPowersBot C) n

theorem forms_finite [Algebra.EssFiniteType k C] (n : ℕ) :
    Module.Finite C (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W C ⊥ (dividedPowersBot C) n) := by
  let : Module.Finite C (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form k C ⊥ (dividedPowersBot C) n) :=
    DifferentialFormFiniteness.pdForms_finite k C ⊥ (dividedPowersBot C) n
  exact Module.Finite.of_surjective (formsEquiv p k C n).symm.toLinearMap (formsEquiv p k C n).symm.surjective

theorem frame_forms_finite [Fintype k] [CharP k p] [Algebra.EssFiniteType k C] (n : ℕ) :
    let U := LevelFrame.frame p k C
    letI : Algebra W U.ring := U.base.toAlgebra
    Module.Finite U.ring (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W U.ring U.ideal U.dividedPowers n) :=
  forms_finite p k C n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.FormFiniteness
