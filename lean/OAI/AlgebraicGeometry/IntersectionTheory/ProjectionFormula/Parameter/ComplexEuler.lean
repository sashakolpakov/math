import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TorKernel

/-! # Complex Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ComplexEuler

noncomputable section

/-! Alternating homology lengths after reduction modulo a regular
parameter equal the sum of the native principal Tor Euler
characteristics of the original homology modules. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientComplex

variable (R : Type u) [CommRing R] (r : R)
  (K : ChainComplex (ModuleCat.{u} R) ℕ)
  (hr : ∀ i, IsSMulRegular (K.X i) r)

def quotientLength (i : ℕ) : ℚ :=
  (Module.length R (QuotSMulTop r (K.homology i))).toNat

def torsionLength (i : ℕ) : ℚ :=
  (Module.length R (LinearMap.ker (LinearMap.lsmul R (K.homology i) r))).toNat

include hr

theorem degree_zero : ExactLength.rationalLength R ((QuotientComplex.complex R r K).homology 0) =
    quotientLength R r K 0 := by
  exact congrArg (fun a : ℕ∞ => (a.toNat : ℚ))
    (Homology.zeroEquiv R r K hr).length_eq.symm

theorem degree_succ (i : ℕ)
    (hfin : Module.length R ((QuotientComplex.complex R r K).homology (i + 1)) ≠ ⊤) :
    ExactLength.rationalLength R ((QuotientComplex.complex R r K).homology (i + 1)) =
      quotientLength R r K (i + 1) + torsionLength R r K i := by
  let S := Homology.sequence R r K hr i
  have hS := Homology.sequence_shortExact R r K hr i
  have hinj := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hsurj := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  have he := Module.length_eq_add_of_exact S.f.hom S.g.hom hinj hsurj
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
  have hleft : Module.length R S.X₁ ≠ ⊤ := ne_top_of_le_ne_top hfin
    (Module.length_le_of_injective S.f.hom hinj)
  have hright : Module.length R S.X₃ ≠ ⊤ := ne_top_of_le_ne_top hfin
    (Module.length_le_of_surjective S.g.hom hsurj)
  change ((Module.length R S.X₂).toNat : ℚ) =
    (Module.length R S.X₁).toNat + (Module.length R S.X₃).toNat
  rw [he, ENat.toNat_add hleft hright, Nat.cast_add]

theorem torsion_top_zero (d : ℕ) (hd : IsZero ((QuotientComplex.complex R r K).homology (d + 1))) :
    torsionLength R r K d = 0 := by
  let S := Homology.sequence R r K hr d
  have hS := Homology.sequence_shortExact R r K hr d
  let : Subsingleton S.X₂ := ModuleCat.subsingleton_of_isZero hd
  have hle := Module.length_le_of_surjective S.g.hom
    ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)
  have hzero : Module.length R S.X₃ = 0 := by
    have hz₂ : Module.length R S.X₂ = 0 := Module.length_eq_zero
    rw [hz₂] at hle
    exact le_antisymm hle zero_le
  change ((Module.length R S.X₃).toNat : ℚ) = 0
  simp only [hzero, ENat.toNat_zero, Nat.cast_zero]

omit hr in
theorem alternating (b q t : ℕ → ℚ) (h₀ : b 0 = q 0)
    (hs : ∀ n, b (n + 1) = q (n + 1) + t n) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * b i) =
      (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * (q i - t i)) +
        (-1 : ℚ) ^ d * t d := by
  induction d with
  | zero => simp [h₀]
  | succ d ih =>
    rw [Finset.sum_range_succ (n := d + 1), Finset.sum_range_succ (n := d + 1), ih, hs]
    simp only [pow_succ]
    ring

theorem euler (hregular : IsSMulRegular R r)
    (hfin : ∀ i, Module.length R ((QuotientComplex.complex R r K).homology i) ≠ ⊤)
    (d : ℕ) (hd : IsZero ((QuotientComplex.complex R r K).homology (d + 1))) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      ExactLength.rationalLength R ((QuotientComplex.complex R r K).homology i)) =
    ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      Tor.Euler.euler R (K.homology i) (.of R (QuotSMulTop r R)) 1 := by
  have he := alternating (fun i => ExactLength.rationalLength R ((QuotientComplex.complex R r K).homology i))
    (quotientLength R r K) (torsionLength R r K) (degree_zero R r K hr)
    (fun i => degree_succ R r K hr i (hfin (i + 1))) d
  rw [torsion_top_zero R r K hr d hd, mul_zero, add_zero] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [TorKernel.euler R r hregular]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ComplexEuler
