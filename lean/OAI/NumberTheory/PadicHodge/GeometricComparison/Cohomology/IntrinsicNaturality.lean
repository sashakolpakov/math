import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.FractionNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.SmallNaturality

/-! # Intrinsic Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The constructed crystalline/de Rham comparison intertwines every actual extending endomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

theorem Cohomology.IntrinsicNaturality.conjugated_naturality {V W Z : Type*} (e : V ≃ W) (c : V → Z)
    (T : V → V) (U : W → W) (S : Z → Z)
    (he : ∀ v, e (T v) = U (e v)) (hc : ∀ v, c (T v) = S (c v)) (w : W) :
    c (e.symm (U w)) = S (c (e.symm w)) := by
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [← he, e.symm_apply_apply, e.symm_apply_apply]
  exact hc v

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.fractionComparison_naturality (hCohomology : Cohomology.Good.GoodReductionInput.{0})
    (f : A.ExtendingEndomorphism) (x : A.SmallCrystalline) :
    A.fractionComparison hCohomology (A.smallCrystallinePullback f x) =
      AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.deRhamPullback (DVR.PadicBase.dvr q) f.integral.toMul.hom.hom 1
        (A.fractionComparison hCohomology x) := by
  have h := congrArg (fun y => A.e62Comparison hCohomology (1 ⊗ₜ[(DVR.PadicBase.dvr q).K₀] y))
    (LinearMap.congr_fun (A.e62SmallEquiv_naturality f) x)
  exact (A.fractionComparison_apply hCohomology (A.smallCrystallinePullback f x)).trans
    (h.trans (A.e62Comparison_naturality hCohomology f (1 ⊗ₜ[(DVR.PadicBase.dvr q).K₀] A.e62SmallEquiv x)))

theorem Geometry.AbelianH1Model.smallToDeRhamEquiv_naturality (hCohomology : Cohomology.Good.GoodReductionInput.{0})
    (f : A.ExtendingEndomorphism) (x : A.SmallCrystalline) :
    A.smallToDeRhamEquiv hCohomology (A.smallCrystallinePullback f x) =
      A.deRhamPullback f (A.smallToDeRhamEquiv hCohomology x) :=
  (congrArg A.fractionDeRhamEquiv (A.fractionComparison_naturality hCohomology f x)).trans
    (A.fractionDeRhamEquiv_naturality f (A.fractionComparison hCohomology x))

theorem Geometry.AbelianH1Model.crystallineDeRhamEquiv_naturality (hCohomology : Cohomology.Good.GoodReductionInput.{0})
    (f : A.ExtendingEndomorphism) (x : A.Crystalline) :
    A.crystallineDeRhamEquiv hCohomology (A.crystallinePullback f x) =
      A.deRhamPullback f (A.crystallineDeRhamEquiv hCohomology x) :=
  Cohomology.IntrinsicNaturality.conjugated_naturality A.smallCrystallineEquiv.toEquiv (A.smallToDeRhamEquiv hCohomology)
    (A.smallCrystallinePullback f) (A.crystallinePullback f) (A.deRhamPullback f)
    (A.smallCrystallineEquiv_pullback f) (A.smallToDeRhamEquiv_naturality hCohomology f) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
