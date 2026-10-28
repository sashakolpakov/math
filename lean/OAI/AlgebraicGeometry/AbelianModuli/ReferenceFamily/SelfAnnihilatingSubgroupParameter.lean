import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleSubgroupContainment
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeAnnihilator

/-! # Self Annihilating Subgroup Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SelfAnnihilatingSubgroupParameter

noncomputable section

/-! The full self-annihilation condition for an actual multiplicative
pairing cuts out a clopen subparameter. The annihilator model is
constructed through the pairing's own roots-of-unity factorization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeAnnihilator.Construction

theorem exists_self_annihilating_subgroup_parameter
    {S : Scheme.{0}} {H T : Over S} [GrpObj H]
    [IsFinite H.hom] [Etale H.hom]
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := H) (B := H) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (n : ℕ) (hH : (𝟙 H) ^ n = 1)
    (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x))
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H T) (R : F.Model) :
    ∃ (Q : Over S) (j : Q ⟶ T),
      IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      ∀ (U : Over S) (f : U ⟶ T),
        (∃! g : U ⟶ Q, g ≫ j = f) ↔
          e.relativeAnnihilator (F.baseChange f) = F.baseChange f := by
  let : Etale R.toBase.left := AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.etale R
  obtain ⟨RA⟩ := AbelianScheme.IsogenyQuotient.MultiplicativeAnnihilator.Construction.multiplicative_pairing_annihilator_has_model e n hH hn F R
  refine ⟨Finite.EtaleSubgroupContainment.FiniteEtaleSubgroupEquality.carrier RA R,
    Finite.EtaleSubgroupContainment.FiniteEtaleSubgroupEquality.inclusion RA R, inferInstance, inferInstance, ?_⟩
  intro U f
  rw [Finite.EtaleSubgroupContainment.FiniteEtaleSubgroupEquality.classifies, e.relativeAnnihilator_baseChange]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SelfAnnihilatingSubgroupParameter
