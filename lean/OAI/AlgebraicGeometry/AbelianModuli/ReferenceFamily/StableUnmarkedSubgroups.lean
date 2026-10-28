import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableSubgroup
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionSubgroupStability
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.RepresentabilityAnd

/-! # Stable Unmarked Subgroups -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableUnmarkedSubgroups

noncomputable section

/-! The actual unmarked torsion-subgroup parameter admits a finite étale
clopen subparameter for stability under finitely many given group
endomorphisms. Its universal subgroup and all-test classifiers are
constructed without a global torsion marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

theorem exists_finite_etale_stable_unmarked_subgroup_parameter
    {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] (n : ℕ)
    (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s))
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    {I : Type*} [Finite I] (e : I → (A ⟶ A)) [∀ i, IsMonHom (e i)] :
    ∃ (Q : Over S) (U : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice A n M Q),
      IsFinite Q.hom ∧ Etale Q.hom ∧
      (∀ i, SubgroupStability.RelativeSubgroupStable U.subgroup (e i)) ∧
      ∀ (T : Over S) (G : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice A n M T),
        (∀ i, SubgroupStability.RelativeSubgroupStable G.subgroup (e i)) ↔
          ∃! f : T ⟶ Q, U.baseChange f = G := by
  obtain ⟨htf, hte⟩ := AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale A n hn
  let : IsFinite (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := htf
  let : Etale (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := hte
  let P := AbelianScheme.TorsionQuotient.RepresentabilityAnd.Representability.parameter A n M
  let U := AbelianScheme.TorsionQuotient.RepresentabilityAnd.Representability.universal A n M
  have hP := AbelianScheme.TorsionQuotient.RepresentabilityAnd.Representability.finite_etale_parameter A n M
  let : IsFinite P.hom := hP.1
  let : Etale P.hom := hP.2.1
  let R := AbelianScheme.TorsionQuotient.Subgroups.TorsionSubgroups.restrictModel A n U.geometric.some U.killed
  let d (i : I) := TorsionSubgroupStability.torsionEndomorphism A n (e i)
  let Q := StableSubgroup.StableSubgroupParameter.carrier R d
  let j : Q ⟶ P := StableSubgroup.StableSubgroupParameter.inclusion R d
  have hcrit {T : Over S} (f : T ⟶ P) :
      (∃! a : T ⟶ Q, a ≫ j = f) ↔
        ∀ i, SubgroupStability.RelativeSubgroupStable (U.baseChange f).subgroup (e i) := by
    refine (StableSubgroup.StableSubgroupParameter.classifies R d f).trans ?_
    apply forall_congr'
    intro i
    change SubgroupStability.RelativeSubgroupStable
        (AbelianScheme.TorsionQuotient.Subgroups.TorsionSubgroups.restrict A n (U.baseChange f).subgroup)
        (TorsionSubgroupStability.torsionEndomorphism A n (e i)) ↔ _
    exact TorsionSubgroupStability.relativeSubgroupStable_torsion_iff A n (e i)
      (U.baseChange f).subgroup (U.baseChange f).killed
  have hU : ∀ i, SubgroupStability.RelativeSubgroupStable (U.baseChange j).subgroup (e i) :=
    (hcrit j).mp ⟨𝟙 Q, Category.id_comp j,
      fun a ha => (cancel_mono j).mp (ha.trans (Category.id_comp j).symm)⟩
  refine ⟨Q, U.baseChange j, inferInstance, inferInstance, hU, ?_⟩
  intro T G
  constructor
  · intro hG
    obtain ⟨f, hf⟩ := AbelianScheme.TorsionQuotient.RepresentabilityAnd.Representability.points_surjective A n M T G
    change U.baseChange f = G at hf
    have hs : ∀ i, SubgroupStability.RelativeSubgroupStable (U.baseChange f).subgroup (e i) := hf.symm ▸ hG
    obtain ⟨g, hg, huniq⟩ := (hcrit f).mpr hs
    have hv : (U.baseChange j).baseChange g = G :=
      (U.baseChange_comp j g).symm.trans ((congrArg U.baseChange hg).trans hf)
    refine ⟨g, hv, ?_⟩
    intro k hk
    apply huniq
    apply AbelianScheme.TorsionQuotient.RepresentabilityAnd.Representability.points_injective A n M T
    change U.baseChange (k ≫ j) = U.baseChange f
    rw [U.baseChange_comp j k, hk, hf]
  · rintro ⟨f, hf, _⟩ i
    have h := SubgroupStability.relativeSubgroupStable_baseChange (e i) (hU i) f
    change SubgroupStability.RelativeSubgroupStable ((U.baseChange j).baseChange f).subgroup (e i) at h
    exact hf ▸ h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableUnmarkedSubgroups
