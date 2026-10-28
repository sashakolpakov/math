import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrelationFamilies
import OAI.RepresentationTheory.Weil.AdelicSplitting.WeylMidpoint

/-! # Correlation Theta -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! The rational sum of midpoint correlations is the product of theta sums. -/

open scoped Classical _root_.NumberField ComplexConjugate

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.correlation_value_rational (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (q x : Fin N → F) :
    (f.correlation F N h q).value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (x i)) =
      f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) ((x - q) i)) *
        conj (h.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) ((x + q) i))) := by
  rw [RestrictedTestFamilies.Construction.RestrictedTestFamily.correlation_value]
  simp only [Pi.sub_apply, Pi.add_apply, map_sub, map_add]
  rfl

theorem CorrelationTheta.Construction.tsum_midpoint_product (ff hh : (Fin N → F) → ℂ)
    (hf : Summable (fun x => ‖ff x‖)) (hh' : Summable (fun x => ‖hh x‖)) :
    (∑' q : Fin N → F, ∑' x : Fin N → F, ff (x - q) * hh (x + q)) =
      (∑' x, ff x) * (∑' x, hh x) := by
  have hs := summable_mul_of_summable_norm hf hh'
  have hc := hs.comp_injective (WeylMidpoint.Construction.correlationPairEquiv F N).injective
  change Summable (fun z : (Fin N → F) × (Fin N → F) => ff (z.2 - z.1) * hh (z.2 + z.1)) at hc
  rw [← hc.tsum_prod]
  change (∑' z : (Fin N → F) × (Fin N → F),
    ff ((WeylMidpoint.Construction.correlationPairEquiv F N z).1) * hh ((WeylMidpoint.Construction.correlationPairEquiv F N z).2)) = _
  exact ((WeylMidpoint.Construction.correlationPairEquiv F N).tsum_eq (fun z => ff z.1 * hh z.2)).trans
    (tsum_mul_tsum_of_summable_norm hf hh').symm

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.tsum_correlation_theta (f h : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (∑' q : Fin N → F, (f.correlation F N h q).theta F N) = f.theta F N * conj (h.theta F N) := by
  let ff (x : Fin N → F) := f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (x i))
  let hh (x : Fin N → F) := conj (h.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (x i)))
  have hf : Summable (fun x => ‖ff x‖) := f.theta_norm_summable F N
  have hh' : Summable (fun x => ‖hh x‖) := by
    simpa only [hh, RCLike.norm_conj] using h.theta_norm_summable F N
  have hc : (∑' q : Fin N → F, (f.correlation F N h q).theta F N) =
      ∑' q : Fin N → F, ∑' x : Fin N → F, ff (x - q) * hh (x + q) := by
    apply tsum_congr
    intro q
    apply tsum_congr
    intro x
    exact f.correlation_value_rational F N h q x
  have htf : (∑' x, ff x) = f.theta F N := rfl
  have hth : (∑' x, hh x) = conj (h.theta F N) :=
    (Complex.conj_tsum (fun x : Fin N → F => h.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (x i)))).symm
  exact hc.trans ((CorrelationTheta.Construction.tsum_midpoint_product F N ff hh hf hh').trans (congrArg₂ (· * ·) htf hth))

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
