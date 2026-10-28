import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RetractionNeighborhood
import Mathlib.RingTheory.Localization.Ideal

/-! # Unramified Quotient Section -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.UnramifiedQuotientSection.Construction

noncomputable section

/-! Lifting a section neighborhood from a quotient to its actual ambient affine ring. -/

variable {H S : Type*} [CommRing H] [CommRing S] [Algebra H S]

/-- A split unramified quotient becomes the base ring after one principal
restriction of the ambient ring; the whole section lies in that restriction. -/
theorem exists_unramified_quotient_section_neighborhood
    (I : Ideal S) (r : S →ₐ[H] H) (hI : I ≤ RingHom.ker r)
    [Algebra.EssFiniteType H (S ⧸ I)] [Algebra.FormallyUnramified H (S ⧸ I)] :
    ∃ (s : S) (e : (Localization.Away s ⧸ I.map (algebraMap S (Localization.Away s))) ≃ₐ[H] H),
      r s = 1 ∧ e.toRingHom.comp
        ((Ideal.Quotient.mk (I.map (algebraMap S (Localization.Away s)))).comp
          (algebraMap S (Localization.Away s))) = r.toRingHom := by
  let Q := S ⧸ I
  let rQ : Q →ₐ[H] H := Ideal.Quotient.liftₐ I r (fun a ha => hI ha)
  obtain ⟨t, e, ht, he⟩ := Etale.RetractionNeighborhood.Construction.exists_unramified_retraction_localization rQ
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  let A := Localization.Away s
  let J := I.map (algebraMap S A)
  let B := A ⧸ J
  have hpow : Algebra.algebraMapSubmonoid Q (Submonoid.powers s) =
      Submonoid.powers (Ideal.Quotient.mk I s) :=
    Submonoid.map_powers _ _
  let : IsLocalization.Away (Ideal.Quotient.mk I s) B := by
    change IsLocalization (Submonoid.powers (Ideal.Quotient.mk I s)) B
    rw [← hpow]
    infer_instance
  let : IsScalarTower H Q B := IsScalarTower.of_algebraMap_eq' (by
    ext h
    change algebraMap H B h = algebraMap Q B (algebraMap H Q h)
    rw [IsScalarTower.algebraMap_apply H S Q, ← IsScalarTower.algebraMap_apply S Q B]
    exact IsScalarTower.algebraMap_apply H S B h)
  let α : B ≃ₐ[Q] Localization.Away (Ideal.Quotient.mk I s) :=
    IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I s)) B _
  let β : B ≃ₐ[H] H := (α.restrictScalars H).trans e
  refine ⟨s, β, ht, ?_⟩
  apply RingHom.ext
  intro a
  change e (α (algebraMap Q B (Ideal.Quotient.mk I a))) = r a
  rw [α.commutes]
  exact RingHom.congr_fun he (Ideal.Quotient.mk I a)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.UnramifiedQuotientSection.Construction
