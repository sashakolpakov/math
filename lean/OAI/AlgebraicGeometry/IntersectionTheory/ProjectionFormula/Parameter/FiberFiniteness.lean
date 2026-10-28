import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.FiniteLength
import Mathlib.RingTheory.Spectrum.Prime.Module

/-! # Fiber Finiteness -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FiberFiniteness

noncomputable section

/-! A parameter fiber whose two input supports intersect at at most
one prime has finite native Tor lengths over the quotient ring. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (r : R)
  (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]

omit [IsNoetherianRing R] in
theorem support_image (p : PrimeSpectrum (ScalarQuotient.Ring R r))
    (hp : p ∈ Module.support (ScalarQuotient.Ring R r) ((ScalarQuotient.quotient R r).obj M) ∩
      Module.support (ScalarQuotient.Ring R r) ((ScalarQuotient.quotient R r).obj N)) :
    PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {r})) p ∈
      (Module.support R M ∩ Module.support R N) ∩
        Module.support R (ScalarQuotient.Ring R r) := by
  have hM := Module.support_subset_preimage_comap (R := R) (A := ScalarQuotient.Ring R r)
    (M := QuotSMulTop r M) hp.1
  have hN := Module.support_subset_preimage_comap (R := R) (A := ScalarQuotient.Ring R r)
    (M := QuotSMulTop r N) hp.2
  rw [Module.support_quotSMulTop] at hM hN
  refine ⟨⟨hM.1, hN.1⟩, ?_⟩
  rw [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  exact Ideal.span_le.mpr hM.2

theorem length_ne_top (p₀ : PrimeSpectrum R)
    (hisolated : (Module.support R M ∩ Module.support R N) ∩
      Module.support R (ScalarQuotient.Ring R r) ⊆ {p₀}) (i : ℕ) :
    Module.length (ScalarQuotient.Ring R r)
      (((Tor (ModuleCat (ScalarQuotient.Ring R r)) i).obj ((ScalarQuotient.quotient R r).obj M)).obj
        ((ScalarQuotient.quotient R r).obj N)) ≠ ⊤ := by
  let S := ScalarQuotient.Ring R r
  let A := (ScalarQuotient.quotient R r).obj M
  let B := (ScalarQuotient.quotient R r).obj N
  let T := ((Tor (ModuleCat S) i).obj A).obj B
  let : Module.Finite S A := Module.Finite.of_restrictScalars_finite R S (QuotSMulTop r M)
  let : Module.Finite S B := Module.Finite.of_restrictScalars_finite R S (QuotSMulTop r N)
  let : Module.Finite S T := ProjectionFormula.Finite.Tor.finite S A B i
  have himage (p : PrimeSpectrum S) (hp : p ∈ Module.support S T) :
      PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {r})) p = p₀ :=
    Set.mem_singleton_iff.mp (hisolated
      (support_image R r M N p (ProjectionFormula.Tor.Support.support_subset S A B i hp)))
  let : Subsingleton (Module.support S T) := ⟨fun p q => by
    apply Subtype.ext
    apply PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    exact (himage p p.property).trans (himage q q.property).symm⟩
  exact Module.length_ne_top_iff.mpr
    (ProjectionFormula.Tor.FiniteLength.finiteLength_of_support_subsingleton S T)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FiberFiniteness
