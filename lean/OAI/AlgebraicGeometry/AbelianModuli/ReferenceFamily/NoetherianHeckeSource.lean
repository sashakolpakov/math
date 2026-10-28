import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableIsotropicSubgroupParameter
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.SubgroupStability
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.RelativePEL
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Descent

/-! # Noetherian Hecke Source -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NoetherianHeckeSource

noncomputable section

/-! The original Noetherian PEL family has a finite etale parameter
for stable self-annihilating subgroups of any prescribed finite module
type. Its universal subgroup has a constructed full PEL quotient.
This constructs the source projection; etaleness of a later map to
the PEL moduli space is a separate assertion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

theorem exists_noetherian_pel_hecke_source
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left]
    (A : PEL.Objects.PELObject P iota N T) (n : ℕ) (hn : 0 < n)
    (hN : Nat.Coprime n N) (hδ : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M] :
    ∃ (Q : Over T.left) (U : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice A.polarized.abelian.scheme n M Q),
      IsFinite Q.hom ∧ Etale Q.hom ∧
      (∀ a, SubgroupStability.RelativeSubgroupStable U.subgroup (A.action.map a)) ∧
      (let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
          (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.polarized.abelian.scheme n) U.subgroup
       (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
          A.polarized.polarization n hn).relativeAnnihilator H = H) ∧
      AbelianScheme.IsogenyQuotient.Noetherian.RelativePEL.Construction.RelativePELQuotient A Q U.subgroup n ∧
      ∀ (X : Over T.left) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice A.polarized.abelian.scheme n M X),
        ((∀ a, SubgroupStability.RelativeSubgroupStable F.subgroup (A.action.map a)) ∧
          (let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
              (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.polarized.abelian.scheme n) F.subgroup
           (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
              A.polarized.polarization n hn).relativeAnnihilator H = H)) ↔
          ∃! f : X ⟶ Q, U.baseChange f = F := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let b := NumberField.RingOfIntegers.basis E
  let e := AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
    A.polarized.polarization n hn
  obtain ⟨Q, U, hQf, hQe, hUs, hUl, hclass⟩ :=
    StableIsotropicSubgroupParameter.exists_stable_self_annihilating_unmarked_subgroup_parameter
      A.polarized.abelian.scheme n (TorsionEtaleAt.TorsionEtale.integer_unit_at_stalk T.hom n) M
      (fun i => A.action.map (b i)) e
  let : IsFinite Q.hom := hQf
  let : Etale Q.hom := hQe
  let : IsLocallyNoetherian Q.left := LocallyOfFiniteType.isLocallyNoetherian Q.hom
  have hUa : ∀ a, SubgroupStability.RelativeSubgroupStable U.subgroup (A.action.map a) :=
    Integral.SubgroupStability.relativeSubgroupStable_action_of_basis A.polarized.abelian A.action U.subgroup b hUs
  have hquot : AbelianScheme.IsogenyQuotient.Noetherian.RelativePEL.Construction.RelativePELQuotient A Q U.subgroup n :=
    AbelianScheme.IsogenyQuotient.Noetherian.RelativePEL.Construction.noetherian_relative_pel_quotient_from_FiniteDescent A Q U.subgroup U.geometric.some n hn U.killed
      hN hδ hUa hUl AbelianScheme.IsogenyQuotient.Finite.Descent.Construction.verifiedFiniteDescentInput
  refine ⟨Q, U, hQf, hQe, hUa, hUl, hquot, ?_⟩
  intro X F
  rw [Integral.SubgroupStability.relativeSubgroupStable_action_iff_basis A.polarized.abelian A.action F.subgroup b]
  exact hclass X F

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NoetherianHeckeSource
