import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistSectionGenerators
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FixedNegativeQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence

/-! # Global Generation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalGeneration

noncomputable section

/-! Every sufficiently positive twist of a coherent projective module has finite global generators. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators
namespace Dimension

universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra

local instance projectiveGlobalGenerationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem positiveTwist_hasFiniteGlobalGenerators (j : σ) (n : ℕ) :
    FiniteGlobalGenerators.HasFiniteGlobalGenerators (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) :=
  ⟨σ, inferInstance, PositiveTwistSectionGenerators.Dimension.positiveTwistGeneratingSection j n, PositiveTwistSectionGenerators.Dimension.positiveTwistGeneratingSection_epi j n⟩

theorem projective_eventually_hasFiniteGlobalGenerators
    (M : (Proj (MvPolynomial.homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → FiniteGlobalGenerators.HasFiniteGlobalGenerators
      (M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) := by
  classical
  obtain ⟨r, d, q, hq⟩ := FixedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient M j
  have := hq
  refine ⟨Finset.univ.sup d, fun n hn => ?_⟩
  let T := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  let N := fun i : Fin r => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)
  have hN (i : Fin r) : FiniteGlobalGenerators.HasFiniteGlobalGenerators (T.obj (N i)) := by
    have hi : d i ≤ n := (Finset.le_sup (f := d) (Finset.mem_univ i)).trans hn
    let e : T.obj (N i) ≅ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n - d i) :=
      TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE j (d i) n hi
    exact (positiveTwist_hasFiniteGlobalGenerators j (n - d i)).of_iso e.symm
  have hsum := FiniteGlobalGenerators.HasFiniteGlobalGenerators.coproduct (fun i => T.obj (N i)) hN
  have hsource : FiniteGlobalGenerators.HasFiniteGlobalGenerators (T.obj (∐ N)) :=
    hsum.of_iso (PreservesCoproduct.iso T N).symm
  exact hsource.of_epi (T.map q)

end Dimension

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalGeneration
