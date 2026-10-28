import OAI.NumberTheory.PadicHodge.IntegralComparison.RepresentablePointTopology
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallinePrincipalTopology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift

/-! # Local Frame Point -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalFramePoint

noncomputable section

/-! Original crystalline covering sieves on a local affine frame are maximal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallinePrincipalTopology

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  (P : BigCrystallineSite.Object p B J δ f) [IsLocalRing P.ring]

theorem principal_factor {U : BigCrystallineSite.Object p B J δ f} {ι : Type u}
    (a : ι → U.ring) (ha : Ideal.span (Set.range a) = ⊤) (g : P ⟶ U) :
    ∃ i, IsUnit (g.ringMap (a i)) := by
  classical
  by_contra! h
  have hle : Ideal.span (Set.range a) ≤ (IsLocalRing.maximalIdeal P.ring).comap g.ringMap.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  rw [ha, top_le_iff] at hle
  have hmem : (1 : U.ring) ∈ (IsLocalRing.maximalIdeal P.ring).comap g.ringMap.toRingHom :=
    hle.symm ▸ (show (1 : U.ring) ∈ (⊤ : Ideal U.ring) from trivial)
  change ¬ IsUnit (g.ringMap.toRingHom 1) at hmem
  rw [map_one] at hmem
  exact hmem isUnit_one

theorem topology_le : BigCrystallineSite.Object.topology ≤ RepresentablePointTopology.topology P := by
  rw [BigCrystallinePrincipalTopology.topology_eq_principal]
  apply RepresentablePointTopology.generated_le
  intro U R hR g
  obtain ⟨ι, a, ha, rfl⟩ := hR
  obtain ⟨i, hi⟩ := principal_factor P a ha g
  exact ⟨Localization.object U (a i), Localization.hom U (a i),
    Presieve.ofArrows.mk i, LocalizationLift.liftHom g (a i) hi,
      LocalizationLift.liftHom_comp g (a i) hi⟩

theorem covering_eq_top (S : Sieve P) (hS : S ∈ BigCrystallineSite.Object.topology P) : S = ⊤ :=
  RepresentablePointTopology.covering_eq_top P BigCrystallineSite.Object.topology (topology_le P) S hS

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalFramePoint
