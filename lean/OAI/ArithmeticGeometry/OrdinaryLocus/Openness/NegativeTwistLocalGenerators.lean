import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CoproductSectionImages
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation

/-! # Negative Twist Local Generators -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistLocalGenerators.Construction

noncomputable section

/-! The local frame images of an actual negative-twist quotient generate all affine sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory Opposite _root_.MvPolynomial

universe u

local instance negativeTwistLocalGeneratorsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance negativeTwistLocalGeneratorsBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def negativeTwistPresentationLocalGenerators
    {N : (Proj (homogeneousSubmodule σ R)).Modules} (j : σ) {r : ℕ} (d : Fin r → ℕ)
    (q : (∐ fun i => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)) ⟶ N) :
    Fin r → Γ(N, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) := fun i =>
  (Sigma.ι _ i ≫ q).app (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) (AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j (d i))

omit [Fintype σ] in
theorem negativeTwistPresentationLocalGenerators_span
    {N : (Proj (homogeneousSubmodule σ R)).Modules} [N.IsQuasicoherent]
    (j : σ) {r : ℕ} (d : Fin r → ℕ)
    (q : (∐ fun i => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)) ⟶ N) [Epi q] :
    Submodule.span Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      (Set.range (negativeTwistPresentationLocalGenerators j d q)) = ⊤ := by
  let Y := Proj (homogeneousSubmodule σ R)
  let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let M := fun i : Fin r => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)
  let F : Y.Modules ⥤ ModuleCat Γ(Y, U) := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  have : F.Additive := { map_add := by intros; ext x; rfl }
  have : (∐ M).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent j d
  have hq : Function.Surjective (F.map q) :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_app_surjective_of_epi U (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen j) q
  let S := Submodule.span Γ(Y, U) (Set.range (negativeTwistPresentationLocalGenerators j d q))
  have hr := CoproductSectionImages.Construction.coproduct_observed_range_of_surjective F M q hq (LinearMap.id : F.obj N →ₗ[Γ(Y, U)] F.obj N)
  apply top_unique
  rw [LinearMap.range_id] at hr
  refine hr.le.trans ?_
  apply iSup_le
  intro i
  rintro _ ⟨x, rfl⟩
  let qi : M i ⟶ N := Sigma.ι M i ≫ q
  have hx := AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneIdealChartPowerSection_generates (R := R) j (d i) x
  have he := (congrArg (qi.app U) hx).trans (qi.app_smul _ _)
  change qi.app U x ∈ S
  rw [he]
  exact S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistLocalGenerators.Construction
