import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaScalarKernel
import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest
import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaQuadratic

/-! # Positive Scalar Product -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.PositiveScalarProduct.Construction

noncomputable section

section

/-! Positive theta multipliers define a subgroup of the actual adelic
cover whose intersection with the global circle is trivial. -/

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

def globalPositiveThetaSubgroup : Subgroup (Vacuum.Construction.GlobalCover F N ψ) :=
  (TestFamilyAction.Construction.positiveThetaSubgroup F N ψ).map (Rational.Construction.assembleGlobalCover F N ψ)

theorem mem_globalPositiveThetaSubgroup_iff (a : Vacuum.Construction.GlobalCover F N ψ) :
    a ∈ globalPositiveThetaSubgroup F N ψ ↔
      ∀ f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N, ∃ c : ℝ, 0 < c ∧ ThetaScalarKernel.Construction.globalTheta F N ψ a f = (c : ℂ) * f.theta F N := by
  constructor
  · rintro ⟨b, hb, rfl⟩ f
    exact hb f
  · intro h
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      (CentralProduct.Construction.scalarKernel (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ)) a
    exact ⟨b, h, rfl⟩

theorem globalScalar_mem_positive_iff (v : ArchimedeanAdeles.Construction.Places F) (z : Circle) :
    GlobalKernel.Construction.globalScalar F N ψ v z ∈ globalPositiveThetaSubgroup F N ψ ↔ z = 1 := by
  constructor
  · intro hz
    obtain ⟨f, hf⟩ := PositiveTestFamily.Construction.exists_theta_nonzero F N
    obtain ⟨c, hc, he⟩ := (mem_globalPositiveThetaSubgroup_iff F N ψ _).mp hz f
    rw [ThetaScalarKernel.Construction.globalTheta_scalar] at he
    have hzc : (z : ℂ) = (c : ℂ) := mul_right_cancel₀ hf he
    have hc1 : c = 1 := by
      have hn := congrArg norm hzc
      rw [Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hn
      exact hn.symm
    apply Subtype.ext
    change (z : ℂ) = 1
    simpa only [hc1, Complex.ofReal_one] using hzc
  · rintro rfl
    rw [map_one]
    exact (globalPositiveThetaSubgroup F N ψ).one_mem

theorem globalPositiveTheta_scalar_eq_one (v : ArchimedeanAdeles.Construction.Places F) (a : Vacuum.Construction.GlobalCover F N ψ)
    (ha : a ∈ globalPositiveThetaSubgroup F N ψ)
    (hs : ∃ z : Circle, GlobalKernel.Construction.globalScalar F N ψ v z = a) : a = 1 := by
  obtain ⟨z, rfl⟩ := hs
  rw [(globalScalar_mem_positive_iff F N ψ v z).mp ha, map_one]

theorem rationalLevi_globalPositiveTheta (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N)
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalLevi F N ψ A a) :
    Rational.Construction.assembleGlobalCover F N ψ a ∈ globalPositiveThetaSubgroup F N ψ := by
  obtain ⟨c, hc, htheta⟩ := ThetaTest.Construction.theta_rational_levi_positive F N ψ A a ha
  exact ⟨a, fun f => ⟨c, hc, htheta f⟩, rfl⟩

theorem rationalQuadratic_globalPositiveTheta
    (hc : Continuous ψ) (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalQuadratic F N ψ B a) :
    Rational.Construction.assembleGlobalCover F N ψ a ∈ globalPositiveThetaSubgroup F N ψ := by
  refine ⟨a, fun f => ⟨1, zero_lt_one, ?_⟩, rfl⟩
  simpa only [Complex.ofReal_one, one_mul] using f.theta_rational_quadratic F N ψ hc hp B a ha

end

/-! An actual restricted scalar family with positive theta multipliers
has circle product one. The product is finite by the vacuum normalization. -/

open scoped Classical
open Filter

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

theorem restricted_scalar_positive_hasProd_one
    (a : Rational.Construction.RestrictedCover F N ψ) (ha : a ∈ TestFamilyAction.Construction.positiveThetaSubgroup F N ψ)
    (z : ArchimedeanAdeles.Construction.Places F → Circle) (hz : ∀ v, a v = Vacuum.Construction.scalarAt F N ψ v (z v)) : HasProd z 1 := by
  let s := (eventually_cofinite.mp (Scalars.Construction.restricted_scalar_eventually_one F N ψ a z hz)).toFinset
  let c : Circle := ∏ v ∈ s, z v
  have htail (v : ArchimedeanAdeles.Construction.Places F) (hv : v ∉ s) : z v = 1 := by
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
  have hp : HasProd z c := hasProd_prod_of_ne_finset_one htail
  have hpC : HasProd (fun v => (z v : ℂ)) (c : ℂ) := hp.map Circle.coeHom continuous_subtype_val
  obtain ⟨f, hf⟩ := PositiveTestFamily.Construction.exists_theta_nonzero F N
  obtain ⟨r, hr, he⟩ := ha f
  rw [f.theta_scalar F N ψ a z hz (c : ℂ) hpC] at he
  have hc : (c : ℂ) = (r : ℂ) := mul_right_cancel₀ hf he
  have hr1 : r = 1 := by
    have hh := congrArg norm hc
    rw [Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hh
    exact hh.symm
  have hc1 : c = 1 := by
    apply Subtype.ext
    change (c : ℂ) = 1
    simpa only [hr1, Complex.ofReal_one] using hc
  rwa [hc1] at hp

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.PositiveScalarProduct.Construction
