import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GeneratedAntiholomorphic
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneSpanning
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality

/-! # Generated Injective -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GeneratedInjective.CM.Construction

noncomputable section

/-! Generation by a projective source makes pullback injective on
the actual entire complex H¹, using the proved Hodge decomposition. -/

open _root_.CategoryTheory

theorem generated_deRham_h1_injective (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (A : CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) (hgen : Albanese.Construction.GeneratedClosed.Generates X.presentation A a) :
    Function.Injective (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback a 1).hom := by
  let f := (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback a 1).hom
  have hker (c : A.variety.deRhamCohomology 1) (hz : f c = 0) : c = 0 := by
    have hc : c ∈ A.variety.pureDeRhamSubspace 1 0 ⊔ A.variety.pureDeRhamSubspace 0 1 := by
      rw [OneSpanning.CM.Construction.pureDeRham_one_sup_top]
      trivial
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hc
    have hu' : f u ∈ X.pureDeRhamSubspace 1 0 :=
      Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_mem_pureDeRhamSubspace a 1 0 hu
    have hv' : f v ∈ X.pureDeRhamSubspace 0 1 :=
      Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_mem_pureDeRhamSubspace a 0 1 hv
    have hsum : f u + f v = 0 := by rw [← map_add, huv, hz]
    have huz : f u = 0 := Submodule.disjoint_def.mp
      (Intersection.CM.Construction.pureDeRham_one_disjoint (E := X.analyticModel) (M := X.analyticSpace)) (f u) hu' (by
        rw [eq_neg_of_add_eq_zero_left hsum]
        exact (X.pureDeRhamSubspace 0 1).neg_mem hv')
    have hvz : f v = 0 := by simpa only [huz, zero_add] using hsum
    have hu0 := GeneratedAntiholomorphic.CM.Construction.generated_holomorphic_deRham_kernel X x₀ A a hgen u hu huz
    have hv0 := GeneratedAntiholomorphic.CM.Construction.generated_antiholomorphic_deRham_kernel X x₀ A a hgen v hv hvz
    rw [← huv, hu0, hv0, add_zero]
  intro c d h
  exact sub_eq_zero.mp (hker (c - d) (by rw [map_sub, h, sub_self]))

theorem generated_complexBetti_h1_injective (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (A : CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) (hgen : Albanese.Construction.GeneratedClosed.Generates X.presentation A a) :
    Function.Injective (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback a 1).hom := by
  intro c d h
  apply (A.variety.deRhamBettiIso 1).toLinearEquiv.symm.injective
  apply generated_deRham_h1_injective X x₀ A a hgen
  have hn (u : A.variety.complexCohomology 1) :=
    ConcreteCategory.congr_hom (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_inv_naturality a 1) u
  exact (hn c).symm.trans ((congrArg (X.deRhamBettiIso 1).inv h).trans (hn d))

theorem generated_rationalBetti_h1_injective (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (A : CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) (hgen : Albanese.Construction.GeneratedClosed.Generates X.presentation A a) :
    Function.Injective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom := by
  intro c d h
  apply Betti.Scheme.schemeBettiRationalInclusion_injective A.toOver 1
  apply generated_complexBetti_h1_injective X x₀ A a hgen
  have hn (u : A.variety.rationalCohomology 1) :=
    ConcreteCategory.congr_hom (Betti.Scheme.schemeBettiRationalInclusion_naturality a 1) u
  exact (hn c).symm.trans ((congrArg (Betti.Scheme.schemeBettiRationalInclusion X.toOver 1) h).trans (hn d))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GeneratedInjective.CM.Construction
