import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TorSpecialization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TensorRegular
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationEuler

/-! # Euler Specialization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.EulerSpecialization

noncomputable section

/-! The native Tor Euler characteristic on a regular parameter fiber
equals the alternating sum of principal Tor Euler characteristics
of the original Tor modules. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength

variable (R : Type u) [CommRing R] (r : R)

theorem euler (hregular : IsSMulRegular R r) (M N : ModuleCat.{u} R)
    (hM : IsSMulRegular M r) (hN : IsSMulRegular N r)
    (d : ℕ) [HasProjectiveDimensionLE N d]
    (hfin : ∀ i, Module.length (ScalarQuotient.Ring R r)
      (((Tor (ModuleCat (ScalarQuotient.Ring R r)) i).obj ((ScalarQuotient.quotient R r).obj M)).obj
        ((ScalarQuotient.quotient R r).obj N)) ≠ ⊤) :
    ProjectionFormula.Tor.Euler.euler (ScalarQuotient.Ring R r) ((ScalarQuotient.quotient R r).obj M) ((ScalarQuotient.quotient R r).obj N) d =
      ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
        ProjectionFormula.Tor.Euler.euler R (((Tor (ModuleCat R) i).obj M).obj N)
          (.of R (QuotSMulTop r R)) 1 := by
  obtain ⟨P, hP⟩ := BoundedResolution.exists_bounded_resolution R N d
  let K := TorSpecialization.tensorComplex R M N P
  have hK (i : ℕ) : IsSMulRegular (K.X i) r :=
    TensorRegular.resolution R r M N hM P i
  have hlen (i : ℕ) := TorSpecialization.length R r hregular M N hN P i
  have hfinite (i : ℕ) :
      Module.length R ((QuotientComplex.complex R r K).homology i) ≠ ⊤ := by
    rw [← hlen i]
    exact hfin i
  have hzero : IsZero ((QuotientComplex.complex R r K).homology (d + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    apply HomologicalComplex.ExactAt.of_isZero
    exact (QuotientComplex.quotient R r).map_isZero
      ((tensorLeft M).map_isZero (hP (d + 1) (by omega)))
  have he := ComplexEuler.euler R r K hK hregular hfinite d hzero
  have hleft : ProjectionFormula.Tor.Euler.euler (ScalarQuotient.Ring R r) ((ScalarQuotient.quotient R r).obj M) ((ScalarQuotient.quotient R r).obj N) d =
      ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
        ExactLength.rationalLength R ((QuotientComplex.complex R r K).homology i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun a : ℕ∞ => (-1 : ℚ) ^ i * (a.toNat : ℚ)) (hlen i)
  rw [hleft, he]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun a : ℚ => (-1 : ℚ) ^ i * a)
    (PrimeFiltrationEuler.euler_iso_left R
      (P.isoLeftDerivedObj (tensorLeft M) i) (.of R (QuotSMulTop r R)) 1).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.EulerSpecialization
