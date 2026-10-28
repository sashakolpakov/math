import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.CoordinateSymbols
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ScalarRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorBase

/-! # Scalar Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.ScalarComparison.FreeRelativeScalarComparison

noncomputable section

/-! # Relative free PD forms with the original smaller scalar action -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (W R σ : Type u) [CommRing W] [CommRing R] [Algebra W R]
  (I : Ideal R) (δ : DividedPowers I) [Fintype σ] [LinearOrder σ]

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.derivatives R σ
local notation "hD" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.commute R σ

def complexIso : Koszul.Tensor.KoszulTensor.complex W σ G (fun i => (D i).restrictScalars W) hD ≅
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex (algebraMap W R)
      (PD.DeRham.PDDeRham.complex R G IG γ) := by
  let e := Koszul.ScalarRestriction.KoszulScalarRestriction.complexIso W R G σ D hD
  let f := ((ModuleCat.restrictScalars (algebraMap W R)).mapHomologicalComplex (.up ℕ)).mapIso
    (Poincare.FreeRelativePoincare.complexIso R σ I δ)
  exact e ≪≫ f

theorem word (n : ℕ) (a : G) (v : Fin n → σ) :
    ((complexIso W R σ I δ).hom.f n).hom
      (a ⊗ₜ[W] exteriorPower.ιMulti W n (fun j => Finsupp.single (v j) 1)) =
        PD.DeRham.PDDeRham.symbol R G IG γ a (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 ∘ v) := by
  change ((Poincare.FreeRelativePoincare.complexIso R σ I δ).hom.f n).hom
    (a ⊗ₜ[R] NumberTheory.PadicHodge.PeriodInvariants.ExteriorSemilinearBaseChange.exteriorMap (algebraMap W R) n
      (exteriorPower.ιMulti W n (fun j => Finsupp.single (v j) 1))) = _
  rw [ExteriorBase.ExteriorBaseChangeWords.word]
  exact CoordinateSymbols.FreeRelativeCoordinateSymbols.word R σ I δ n a v

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.ScalarComparison.FreeRelativeScalarComparison
