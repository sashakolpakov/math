import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.TorFinite

/-! # Principal Isolation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PrincipalIsolation

noncomputable section

/-! Native support and principal-quotient isolation descend through
the actual isomorphism of ambient stalks in an open immersion. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem support {Y X : Scheme} (j : Y ⟶ X) [IsOpenImmersion j]
    (A : IrreducibleCloseds Y) (B : IrreducibleCloseds X)
    (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint B)
    (y : Y) (hy : y ∈ (A : Set Y)) (hx : j y ∈ (B : Set X)) :
    Module.support (Y.presheaf.stalk y) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hy) =
      PrimeSpectrum.comap (j.stalkMap y).hom ⁻¹'
        Module.support (X.presheaf.stalk (j y)) (CycleClass.Thom.IntersectionGeometry.localSupportModule X B (j y) hx) := by
  rw [(Stalk.PrimeQuotient.moduleEquiv Y A y hy _ (Stalk.PrimeQuotient.kernelPrime_image Y A y hy)).support_eq,
    (Stalk.PrimeQuotient.moduleEquiv X B (j y) hx _ (Stalk.PrimeQuotient.kernelPrime_image X B (j y) hx)).support_eq]
  ext q
  simp only [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker,
    Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal]
  rw [← StalkSupport.kernelPrime_map j A B hA y hy hx]
  exact Ideal.map_le_iff_le_comap

theorem quotient_support {Y X : Scheme} [IsLocallyNoetherian Y] [IsLocallyNoetherian X]
    (j : Y ⟶ X) [IsOpenImmersion j]
    (A : IrreducibleCloseds Y) (B : IrreducibleCloseds X)
    (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint B)
    (y : Y) (hy : y ∈ (A : Set Y)) (hx : j y ∈ (B : Set X)) (r : X.presheaf.stalk (j y)) :
    Module.support (Y.presheaf.stalk y) (QuotSMulTop (j.stalkMap y r) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hy)) =
      PrimeSpectrum.comap (j.stalkMap y).hom ⁻¹'
        Module.support (X.presheaf.stalk (j y)) (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X B (j y) hx)) := by
  let : Module.Finite (Y.presheaf.stalk y) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hy) :=
    Local.TorFinite.localSupportModule_finite Y A y hy
  let : Module.Finite (X.presheaf.stalk (j y)) (CycleClass.Thom.IntersectionGeometry.localSupportModule X B (j y) hx) :=
    Local.TorFinite.localSupportModule_finite X B (j y) hx
  rw [Module.support_quotSMulTop, Module.support_quotSMulTop, PrincipalIsolation.support j A B hA y hy hx]
  ext q
  simp only [Set.mem_inter_iff, Set.mem_preimage, PrimeSpectrum.mem_zeroLocus,
    Set.singleton_subset_iff, PrimeSpectrum.comap_asIdeal]
  rfl

theorem isolated {Y X : Scheme} [IsLocallyNoetherian Y] [IsLocallyNoetherian X]
    (j : Y ⟶ X) [IsOpenImmersion j]
    (A B : IrreducibleCloseds Y) (A' B' : IrreducibleCloseds X)
    (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint A') (hB : j (CycleClass.Thom.IntersectionGeometry.supportPoint B) = CycleClass.Thom.IntersectionGeometry.supportPoint B')
    (y : Y) (hyA : y ∈ (A : Set Y)) (hyB : y ∈ (B : Set Y))
    (hxA : j y ∈ (A' : Set X)) (hxB : j y ∈ (B' : Set X)) (r : X.presheaf.stalk (j y))
    (hiso : Module.support (Y.presheaf.stalk y)
        (QuotSMulTop (j.stalkMap y r) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hyA)) ∩
      Module.support (Y.presheaf.stalk y) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B y hyB) ⊆
        {IsLocalRing.closedPoint (Y.presheaf.stalk y)}) :
    Module.support (X.presheaf.stalk (j y)) (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X A' (j y) hxA)) ∩
      Module.support (X.presheaf.stalk (j y)) (CycleClass.Thom.IntersectionGeometry.localSupportModule X B' (j y) hxB) ⊆
        {IsLocalRing.closedPoint (X.presheaf.stalk (j y))} := by
  rw [quotient_support j A A' hA y hyA hxA r, PrincipalIsolation.support j B B' hB y hyB hxB] at hiso
  intro p hp
  obtain ⟨q, hq⟩ := (Spec.map (j.stalkMap y)).surjective p
  change PrimeSpectrum.comap (j.stalkMap y).hom q = p at hq
  have hq' : q = IsLocalRing.closedPoint (Y.presheaf.stalk y) :=
    Set.mem_singleton_iff.mp (hiso (by simpa only [Set.mem_inter_iff, Set.mem_preimage, hq] using hp))
  apply Set.mem_singleton_iff.mpr
  rw [← hq, hq']
  apply PrimeSpectrum.ext
  exact IsLocalRing.maximalIdeal_comap (j.stalkMap y).hom

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PrincipalIsolation
