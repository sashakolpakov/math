import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.AffineEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoveredPrincipalExpansion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalCodimension

/-! # Principal Expansion -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PrincipalExpansion

noncomputable section

/-! Proper principal-quotient pairings have the native divisor-order
expansion, without an auxiliary moving condition on filtration primes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

theorem exists_data (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (R : Type) [CommRing R] [IsNoetherianRing R]
    (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (v : PrimeSpectrum R) (hv : V.supportCodimension (Affine.FiltrationAvoidance.support j v) = k)
    (r : R) (hr : r ∉ v.asIdeal) :
    ∃ F : Finset (PrimeSpectrum R),
      (∀ z ∈ F, v.asIdeal ≤ z.asIdeal ∧ r ∈ z.asIdeal ∧ V.supportCodimension (Affine.FiltrationAvoidance.support j z) = k + 1) ∧
      (∀ z, V.supportCodimension (Affine.FiltrationAvoidance.support j z) = k + 1 → z ∉ F →
        Affine.PrincipalWeight.weight R v r z = 0) ∧
      ∀ (p : ℕ) (Z : Finset (IrreducibleCloseds V.carrier))
        (_hZ : ∀ B ∈ Z, k + 1 ≤ V.supportCodimension B)
        (_hcover : ∀ w ∈ Module.support R (QuotSMulTop r (R ⧸ v.asIdeal)),
          ∃ B ∈ Z, j w ∈ (B : Set V.carrier))
        (A : V.DimensionCycleSupport p) (A₀ : IrreducibleCloseds (Spec (.of R)))
        (_hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
        (_hproper : ∀ B ∈ Z, ∀ D : IrreducibleCloseds V.carrier,
          (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B : Set V.carrier) →
            p + V.supportCodimension B ≤ V.supportCodimension D)
        (C : V.DimensionCycleSupport (p + (k + 1))) (x : PrimeSpectrum R)
        (_hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val) (hxA : x ∈ (A₀ : Set (Spec (.of R))))
        (hvx : v.asIdeal ≤ x.asIdeal),
        CoveredPrincipalExpansion.pairing R v r A₀ x hxA hvx m =
          ∑ z ∈ F, Affine.PrincipalWeight.weight R v r z *
            CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity V (Affine.FiltrationAvoidance.support j z) A.val C.val := by
  let M := ModuleCat.of R (QuotSMulTop r (R ⧸ v.asIdeal))
  have hM : ∀ z ∈ Module.support R M, k + 1 ≤ V.supportCodimension (Affine.FiltrationAvoidance.support j z) :=
    Affine.PrincipalCodimension.bound V m k j v hv r hr
  obtain ⟨F, hF, hout, he⟩ := AffineEuler.exists_data V m (k + 1) R j M hM
  refine ⟨F, ?_, ?_, ?_⟩
  · intro z hz
    have h := Affine.PrincipalCodimension.mem_support v z r (hF z hz).1
    exact ⟨h.1, h.2, (hF z hz).2.1⟩
  · intro z hz hnot
    rw [Affine.PrincipalWeight.eq_length_all R v r hr z, hout z hz hnot]
    rfl
  · intro p Z hZ hcover A A₀ hA hproper C x hx hxA hvx
    let : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    unfold CoveredPrincipalExpansion.pairing
    rw [← Affine.PrincipalBaseChange.euler R v x hvx r (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) m,
      he p Z hZ hcover A A₀ hA hproper C x hx hxA]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Affine.PrincipalWeight.eq_length R v r hr z (hF z hz).1]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PrincipalExpansion
