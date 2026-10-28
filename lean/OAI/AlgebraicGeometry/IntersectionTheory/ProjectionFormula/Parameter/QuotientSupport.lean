import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BaseChangeSupport
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Quotient Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientSupport

noncomputable section

/-! Native parameter quotients preserve isolated pair supports.
Their primes strictly specialize any prime on which the parameter
was nonzero, giving the rank drop used in regular-sequence induction. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient

variable (R : Type u) [CommRing R] (r : R)

theorem mem_image (M : ModuleCat.{u} R) [Module.Finite R M] (p : PrimeSpectrum (ScalarQuotient.Ring R r))
    (hp : p ∈ Module.support (ScalarQuotient.Ring R r) ((ScalarQuotient.quotient R r).obj M)) :
    PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {r})) p ∈ Module.support R M := by
  have h := hp
  change p ∈ Module.support (ScalarQuotient.Ring R r) (QuotSMulTop r M) at h
  rw [(ScalarQuotient.baseChangeEquiv R r M).support_eq] at h
  exact BaseChangeSupport.mem_image R (ScalarQuotient.Ring R r) M p h

theorem parameter_mem (p : PrimeSpectrum (ScalarQuotient.Ring R r)) :
    r ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {r})) p).asIdeal := by
  change Ideal.Quotient.mk (Ideal.span {r}) r ∈ p.asIdeal
  rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton r))]
  exact p.asIdeal.zero_mem

theorem isolated [IsLocalRing R] [IsLocalRing (ScalarQuotient.Ring R r)]
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (hiso : Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R}) :
    Module.support (ScalarQuotient.Ring R r) ((ScalarQuotient.quotient R r).obj M) ∩
      Module.support (ScalarQuotient.Ring R r) ((ScalarQuotient.quotient R r).obj N) ⊆ {IsLocalRing.closedPoint (ScalarQuotient.Ring R r)} := by
  let f := Ideal.Quotient.mk (Ideal.span {r})
  let : IsLocalHom f := IsLocalHom.of_surjective f Ideal.Quotient.mk_surjective
  intro p hp
  have he : PrimeSpectrum.comap f p = IsLocalRing.closedPoint R :=
    Set.mem_singleton_iff.mp (hiso ⟨mem_image R r M p hp.1, mem_image R r N p hp.2⟩)
  apply Set.mem_singleton_iff.mpr
  apply PrimeSpectrum.comap_injective_of_surjective f Ideal.Quotient.mk_surjective
  refine he.trans ?_
  apply PrimeSpectrum.ext
  exact (IsLocalRing.maximalIdeal_comap f).symm

theorem rank_strict (ρ : PrimeSpectrum R → ℕ) (hρ : StrictAnti ρ) :
    StrictAnti (fun p : PrimeSpectrum (ScalarQuotient.Ring R r) => ρ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {r})) p)) := by
  intro p q hpq
  apply hρ
  apply lt_of_le_of_ne (Ideal.comap_mono hpq.le)
  intro he
  exact hpq.ne (PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective (PrimeSpectrum.ext he))

theorem rank_drop (ρ : PrimeSpectrum R → ℕ) (hρ : StrictAnti ρ)
    (p : PrimeSpectrum R) (hr : r ∉ p.asIdeal) (q : PrimeSpectrum (ScalarQuotient.Ring R r))
    (hq : q ∈ Module.support (ScalarQuotient.Ring R r) ((ScalarQuotient.quotient R r).obj (.of R (R ⧸ p.asIdeal)))) :
    ρ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {r})) q) < ρ p := by
  have hpq := mem_image R r (.of R (R ⧸ p.asIdeal)) q hq
  rw [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] at hpq
  apply hρ
  apply lt_of_le_of_ne hpq
  intro he
  exact hr (he.symm ▸ parameter_mem R r q)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientSupport
