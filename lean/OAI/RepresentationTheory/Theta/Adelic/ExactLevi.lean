import OAI.RepresentationTheory.Theta.Adelic.RationalGraph
import OAI.RepresentationTheory.Theta.Adelic.LeviConjugation

/-! # Exact Levi -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.ExactLevi

/-! Exact rational Levi theta invariance. Fourier conjugation exchanges a
Levi matrix with its inverse transpose and hence reciprocates its positive
theta multiplier. This forces that multiplier to be one. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.LeviConjugation

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)

theorem theta_levi_of_product (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F N)
    (a : Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ) (ha : Weil.AdelicSplitting.Rational.Construction.IsRationalLevi F N ψ A a)
    (c : ℝ) (hc : HasProd (fun v => (Weil.AdelicSplitting.ThetaTest.Construction.rationalLeviCoefficient F N A v : ℂ)) (c : ℂ))
    (f : Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (f.act F N ψ a).theta F N = (c : ℂ) * f.theta F N := by
  change (∑' q : Fin N → F, (f.act F N ψ a).value F N
    (fun i => algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) (q i))) = _
  simp_rw [f.levi_rational_value F N ψ A a ha c hc]
  rw [tsum_mul_left]
  congr 1
  exact (Weil.AdelicSplitting.LinearSubstitution.LocalAnalysis.positionLinearEquiv A⁻¹).toEquiv.tsum_eq
    (fun q => f.value F N (fun i => algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) (q i)))

variable (hc : Continuous ψ) (hu : ∀ a, ‖ψ a‖ = 1) (hn : ∃ a, ψ a ≠ 1)
variable (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)

include hc hu hn hp

theorem rational_fourier_conjugate_levi (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F N)
    (a : Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ) (ha : Weil.AdelicSplitting.Rational.Construction.IsRationalLevi F N ψ A a) :
    Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F N ψ
      (RationalFourier.rationalFourierFamily F ψ hc hu hn hp N * a *
        (RationalFourier.rationalFourierFamily F ψ hc hu hn hp N)⁻¹) =
      Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F N ψ (Weil.AdelicSplitting.RationalLevi.Construction.rationalLeviFamily F N ψ (LeviConjugation.inverseTranspose A)) := by
  obtain ⟨r, hr, -⟩ := RationalGraph.rationalGraph_realization F N ψ hc hu hn hp
  let W := RationalFourier.rationalFourierFamily F ψ hc hu hn hp N
  have hW : (Weil.Local.Generators.Construction.weylSymplectic F N, Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F N ψ W) ∈ Weil.AdelicSplitting.Rational.Construction.rationalGraph F N ψ :=
    Subgroup.subset_closure (Or.inr (Or.inr
      ⟨W, RationalFourier.rationalFourierFamily_spec F ψ hc hu hn hp N, rfl⟩))
  have hA : (Weil.Local.Generators.Construction.leviSymplectic A, Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F N ψ a) ∈ Weil.AdelicSplitting.Rational.Construction.rationalGraph F N ψ :=
    Subgroup.subset_closure (Or.inl ⟨A, a, ha, rfl⟩)
  have hconj := (Weil.AdelicSplitting.Rational.Construction.rationalGraph F N ψ).mul_mem ((Weil.AdelicSplitting.Rational.Construction.rationalGraph F N ψ).mul_mem hW hA)
    ((Weil.AdelicSplitting.Rational.Construction.rationalGraph F N ψ).inv_mem hW)
  change (Weil.Local.Generators.Construction.weylSymplectic F N * Weil.Local.Generators.Construction.leviSymplectic A * (Weil.Local.Generators.Construction.weylSymplectic F N)⁻¹,
    Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F N ψ W * Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F N ψ a *
      (Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F N ψ W)⁻¹) ∈ Weil.AdelicSplitting.Rational.Construction.rationalGraph F N ψ at hconj
  rw [LeviConjugation.weyl_conjugate_levi] at hconj
  have he := ((hr _ _).mp hconj).symm.trans
    ((hr _ _).mp (Weil.AdelicSplitting.RationalLevi.Construction.rationalGraph_contains_levi F N ψ (LeviConjugation.inverseTranspose A)))
  simpa only [map_mul, map_inv] using he

theorem theta_rational_levi (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F N)
    (a : Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ) (ha : Weil.AdelicSplitting.Rational.Construction.IsRationalLevi F N ψ A a)
    (f : Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N) : (f.act F N ψ a).theta F N = f.theta F N := by
  obtain ⟨c, hcpos, hprod⟩ := Weil.AdelicSplitting.ThetaTest.Construction.rationalLeviCoefficient_positive_product F N ψ A a ha
  let b := Weil.AdelicSplitting.RationalLevi.Construction.rationalLeviFamily F N ψ (LeviConjugation.inverseTranspose A)
  have hb : Weil.AdelicSplitting.Rational.Construction.IsRationalLevi F N ψ (LeviConjugation.inverseTranspose A) b := Weil.AdelicSplitting.RationalLevi.Construction.rationalLeviFamily_spec F N ψ _
  have hprodInv : HasProd (fun v => (Weil.AdelicSplitting.ThetaTest.Construction.rationalLeviCoefficient F N (LeviConjugation.inverseTranspose A) v : ℂ))
      ((c⁻¹ : ℝ) : ℂ) := by
    simpa only [LeviConjugation.rationalLeviCoefficient_inverseTranspose, Complex.ofReal_inv] using
      hprod.inv₀ (Complex.ofReal_ne_zero.mpr hcpos.ne')
  let W := RationalFourier.rationalFourierFamily F ψ hc hu hn hp N
  have hW : W ∈ Weil.AdelicSplitting.TestFamilyAction.Construction.thetaStabilizer F N ψ := RationalFourier.theta_fourier F ψ hc hu hn hp N
  have hWi := (Weil.AdelicSplitting.TestFamilyAction.Construction.thetaStabilizer F N ψ).inv_mem hW
  have he (g : Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N) : (c : ℂ) * g.theta F N = ((c⁻¹ : ℝ) : ℂ) * g.theta F N := by
    have h := Weil.AdelicSplitting.ThetaScalarKernel.Construction.theta_eq_of_assemble_eq F N ψ (W * a * W⁻¹) b
      (rational_fourier_conjugate_levi F N ψ hc hu hn hp A a ha) g
    rw [Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily.act_mul, Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily.act_mul, hW,
      theta_levi_of_product F N ψ A a ha c hprod, hWi,
      theta_levi_of_product F N ψ (LeviConjugation.inverseTranspose A) b hb c⁻¹ hprodInv] at h
    exact h
  obtain ⟨g, hg⟩ := Weil.AdelicSplitting.PositiveTestFamily.Construction.exists_theta_nonzero F N
  have hcc : c = c⁻¹ := Complex.ofReal_injective (mul_right_cancel₀ hg (he g))
  have hsq : c ^ 2 = 1 := by
    calc
      c ^ 2 = c * c := pow_two c
      _ = c * c⁻¹ := congrArg (fun x => c * x) hcc
      _ = 1 := mul_inv_cancel₀ hcpos.ne'
  have hc1 : c = 1 := by nlinarith
  simpa only [hc1, Complex.ofReal_one, one_mul] using theta_levi_of_product F N ψ A a ha c hprod f

end RepresentationTheory.Theta.Adelic.ExactLevi

namespace RepresentationTheory.Theta.Adelic.ExactLevi.RationalTheta

/-! Every element of the actual rational oscillator graph preserves the
convergent theta sum exactly, using the three prescribed generator formulas. -/

open scoped _root_.NumberField Classical

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)

theorem rationalFourierFamily_unique (a b : Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ)
    (ha : Weil.AdelicSplitting.Rational.Construction.IsRationalFourier F N ψ a) (hb : Weil.AdelicSplitting.Rational.Construction.IsRationalFourier F N ψ b) : a = b := by
  apply RestrictedProduct.ext
  intro v
  apply Weil.AdelicSplitting.NormalizationLevi.Construction.localCover_ext
  · exact (ha.1 v).trans (hb.1 v).symm
  · intro f x
    exact (ha.2 v f x).trans (hb.2 v f x).symm

def globalThetaStabilizer : Subgroup (Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F N ψ) :=
  (Weil.AdelicSplitting.TestFamilyAction.Construction.thetaStabilizer F N ψ).map (Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F N ψ)

theorem mem_globalThetaStabilizer_iff (a : Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F N ψ) :
    a ∈ globalThetaStabilizer F N ψ ↔
      ∀ f : Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N, Weil.AdelicSplitting.ThetaScalarKernel.Construction.globalTheta F N ψ a f = f.theta F N := by
  constructor
  · rintro ⟨b, hb, rfl⟩ f
    exact hb f
  · intro h
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      (Weil.AdelicSplitting.CentralProduct.Construction.scalarKernel (Weil.AdelicSplitting.Vacuum.Construction.coverIntegral F N ψ) (Weil.AdelicSplitting.Vacuum.Construction.scalarAt F N ψ)) a
    exact ⟨b, h, rfl⟩

variable (hc : Continuous ψ) (hu : ∀ a, ‖ψ a‖ = 1) (hn : ∃ a, ψ a ≠ 1)
variable (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)

include hc hu hn hp

theorem rationalGraph_stabilizes_theta :
    Weil.AdelicSplitting.Rational.Construction.rationalGraph F N ψ ≤ (globalThetaStabilizer F N ψ).comap (MonoidHom.snd _ _) := by
  change Subgroup.closure (Weil.AdelicSplitting.Rational.Construction.rationalGeneratorPairs F N ψ) ≤ _
  apply (Subgroup.closure_le ((globalThetaStabilizer F N ψ).comap
    (MonoidHom.snd (Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N) (Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F N ψ)))).mpr
  intro z hz
  rcases hz with ⟨A, a, ha, rfl⟩ | ⟨B, a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact ⟨a, theta_rational_levi F N ψ hc hu hn hp A a ha, rfl⟩
  · exact ⟨a, fun f => f.theta_rational_quadratic F N ψ hc hp B a ha, rfl⟩
  · have he := rationalFourierFamily_unique F N ψ a
      (RationalFourier.rationalFourierFamily F ψ hc hu hn hp N) ha
      (RationalFourier.rationalFourierFamily_spec F ψ hc hu hn hp N)
    subst a
    exact ⟨_, RationalFourier.theta_fourier F ψ hc hu hn hp N, rfl⟩

theorem rational_theta (γ : Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N) (a : Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ)
    (ha : (γ, Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F N ψ a) ∈ Weil.AdelicSplitting.Rational.Construction.rationalGraph F N ψ)
    (f : Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N) : (f.act F N ψ a).theta F N = f.theta F N :=
  (mem_globalThetaStabilizer_iff F N ψ _).mp
    (rationalGraph_stabilizes_theta F N ψ hc hu hn hp ha) f

end RepresentationTheory.Theta.Adelic.ExactLevi.RationalTheta

end

end OAI
