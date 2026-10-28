import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.QuotientTensor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TensorRegular
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.EulerTransport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.PrimeEuler

/-! # Quotient Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.QuotientEuler

noncomputable section

/-! The native Euler pairing with a regular principal quotient is
the alternating principal Euler pairing of the original Tor modules.
Only the first module needs parameter regularity. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength

variable (R : Type u) [CommRing R] (r : R)

theorem euler (hregular : IsSMulRegular R r) (M N : ModuleCat.{u} R)
    (hM : IsSMulRegular M r) (d : ℕ) [HasProjectiveDimensionLE N d]
    (hfin : ∀ i, Module.length R
      (((Tor (ModuleCat R) i).obj (.of R (QuotSMulTop r M))).obj N) ≠ ⊤) :
    ProjectionFormula.Tor.Euler.euler R (.of R (QuotSMulTop r M)) N d =
      ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
        ProjectionFormula.Tor.Euler.euler R (((Tor (ModuleCat R) i).obj M).obj N)
          (.of R (QuotSMulTop r R)) 1 := by
  obtain ⟨P, hP⟩ := BoundedResolution.exists_bounded_resolution R N d
  let K := Parameter.TorSpecialization.tensorComplex R M N P
  have hK (i : ℕ) : IsSMulRegular (K.X i) r :=
    Parameter.TensorRegular.resolution R r M N hM P i
  have hlen (i : ℕ) := (QuotientTensor.torIso R r M N P i).toLinearEquiv.length_eq
  have hfinite (i : ℕ) :
      Module.length R ((Parameter.QuotientComplex.complex R r K).homology i) ≠ ⊤ := by
    rw [← hlen i]
    exact hfin i
  have hzero : IsZero ((Parameter.QuotientComplex.complex R r K).homology (d + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    apply HomologicalComplex.ExactAt.of_isZero
    exact (Parameter.QuotientComplex.quotient R r).map_isZero
      ((tensorLeft M).map_isZero (hP (d + 1) (by omega)))
  have he := Parameter.ComplexEuler.euler R r K hK hregular hfinite d hzero
  have hleft : ProjectionFormula.Tor.Euler.euler R (.of R (QuotSMulTop r M)) N d =
      ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
        ExactLength.rationalLength R ((Parameter.QuotientComplex.complex R r K).homology i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun a : ℕ∞ => (-1 : ℚ) ^ i * (a.toNat : ℚ)) (hlen i)
  rw [hleft, he]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun a : ℚ => (-1 : ℚ) ^ i * a)
    (PrimeFiltrationEuler.euler_iso_left R
      (P.isoLeftDerivedObj (tensorLeft M) i) (.of R (QuotSMulTop r R)) 1).symm

theorem isolated [IsNoetherianRing R] (hregular : IsSMulRegular R r)
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (hM : IsSMulRegular M r) (d : ℕ) [HasProjectiveDimensionLE N d]
    (p₀ : PrimeSpectrum R)
    (hisolated : (Module.support R M ∩ Module.support R N) ∩
      Module.support R (R ⧸ Ideal.span {r}) ⊆ {p₀}) :
    ProjectionFormula.Tor.Euler.euler R (.of R (QuotSMulTop r M)) N d =
      ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
        ProjectionFormula.Tor.Euler.euler R (((Tor (ModuleCat R) i).obj M).obj N)
          (.of R (R ⧸ Ideal.span {r})) 1 := by
  have hsupp : Module.support R (QuotSMulTop r M) ∩ Module.support R N ⊆ {p₀} := by
    intro p hp
    have hM := hp.1
    rw [Module.support_quotSMulTop] at hM
    apply hisolated
    refine ⟨⟨hM.1, hp.2⟩, ?_⟩
    rw [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact Ideal.span_le.mpr hM.2
  rw [euler R r hregular M N hM d
    (ProjectionFormula.Tor.FiniteLength.tor_length_ne_top R (.of R (QuotSMulTop r M)) N p₀ hsupp)]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun a : ℚ => (-1 : ℚ) ^ i * a)
    (ProjectionFormula.Tor.EulerTransport.iso_right R _
      (Parameter.PrimeEuler.quotientEquiv R r).symm.toModuleIso 1)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.QuotientEuler
