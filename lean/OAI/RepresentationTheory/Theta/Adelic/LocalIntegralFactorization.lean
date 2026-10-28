import OAI.RepresentationTheory.Theta.Adelic.IntegralUnitaryFactorization
import OAI.RepresentationTheory.Theta.Adelic.IntegralScalarFamily

/-! # Local Integral Factorization -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.LocalIntegralFactorization

/-! The actual integral quadratic order at a finite completion admits
uniform unitary open-cell factorization from the rational scalar family. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients
open OAI.RepresentationTheory.Theta.Adelic.IntegralUnitaryFactorization OAI.RepresentationTheory.Theta.Adelic.IntegralScalarFamily.Family

variable (F : Type) [Field F] [NumberField F] (d : F) (hns : ¬ IsSquare d)
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
variable (hdv : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v))
variable (R N : ℕ) (hR : 2 * N < R)
variable (hz : IntegralScalarFamily.Family.IntegralScalarFamilyAt F d hns R (.inr v))

def LocalIntegralOpenCell (H : Matrix (Fin N) (Fin N) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v))) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H) : Prop :=
  ∃ u : (Matrix (Fin N) (Fin N) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v)))ˣ, u.val = g.val.val - 1 ∧
    (∀ i j, u.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v)) ∧
    (∀ i j, u.inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v))

include hdv hR hz in
theorem local_integral_unitary_factorization
    (H : Matrix (Fin N) (Fin N) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v))) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H)
    (hg : ∀ i j, g.val.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v)) :
    ∃ a b : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H, g = a * b ∧ LocalIntegralOpenCell F d v N H a ∧ LocalIntegralOpenCell F d v N H b := by
  let S := Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)
  let : IsLocalRing S := inferInstanceAs (IsLocalRing (v.adicCompletionIntegers F))
  let dv := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d
  let T := QuadraticIntegralCoefficients.coefficientOrder S dv hdv
  have he (x : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v)) : x ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v) ↔ x ∈ T :=
    QuadraticIntegralCoefficients.quadraticOrder_coefficients F d (.inr v) hdv x
  obtain ⟨a, b, hab, ha, hb⟩ := IntegralUnitaryFactorization.integral_unitary_factorization S dv hdv H g
    (fun i j => (he _).mp (hg i j)) (IntegralScalarFamily.Family.localScalarFamily F d hns R (.inr v))
    (IntegralScalarFamily.Family.localScalarFamily_unitary F d hns R (.inr v))
    (fun i => ⟨(he _).mp (hz.integral i).1, (he _).mp (hz.integral i).2⟩)
    (fun i => by
      obtain ⟨u, hu, hv, hi⟩ := hz.minus_one i
      exact ⟨u, hu, (he _).mp hv, (he _).mp hi⟩)
    (fun i j hij => by
      obtain ⟨u, hu, hv, hi⟩ := hz.differences i j hij
      exact ⟨u, hu, (he _).mp hv, (he _).mp hi⟩)
    (by simpa only [Fintype.card_fin] using hR)
  refine ⟨a, b, hab, ?_, ?_⟩
  · obtain ⟨u, hu, hv, hi⟩ := ha
    exact ⟨u, hu, fun i j => (he _).mpr (hv i j), fun i j => (he _).mpr (hi i j)⟩
  · obtain ⟨u, hu, hv, hi⟩ := hb
    exact ⟨u, hu, fun i j => (he _).mpr (hv i j), fun i j => (he _).mpr (hi i j)⟩

end RepresentationTheory.Theta.Adelic.LocalIntegralFactorization

namespace RepresentationTheory.Theta.Adelic.LocalIntegralFactorization.OpenGeneration

/-! A subgroup containing the integral open cell contains every
integral unitary element at a good finite place. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.IntegralScalarFamily.Family OAI.RepresentationTheory.Theta.Adelic.LocalIntegralFactorization

variable (F : Type) [Field F] [NumberField F] (d : F) (hns : ¬ IsSquare d)
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
variable (hdv : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v))
variable (R N : ℕ) (hR : 2 * N < R)
variable (hz : IntegralScalarFamily.Family.IntegralScalarFamilyAt F d hns R (.inr v))

include hdv hR hz in
theorem integral_unitary_mem_of_open
    (H : Matrix (Fin N) (Fin N) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v))) (U : Subgroup (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H))
    (hU : ∀ g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H, LocalIntegralOpenCell F d v N H g → g ∈ U)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H) (hg : ∀ i j, g.val.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v)) : g ∈ U := by
  obtain ⟨a, b, hab, ha, hb⟩ := local_integral_unitary_factorization F d hns v hdv R N hR hz H g hg
  rw [hab]
  exact U.mul_mem (hU a ha) (hU b hb)

end RepresentationTheory.Theta.Adelic.LocalIntegralFactorization.OpenGeneration

end

end OAI
