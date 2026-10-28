import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableUnmarkedSubgroups
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SelfAnnihilatingSubgroupParameter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport

/-! # Stable Isotropic Subgroup Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableIsotropicSubgroupParameter

noncomputable section

/-! Unmarked stable subgroups equal to their own annihilator form an
actual finite etale parameter. Both conditions are imposed on the
given subgroup functor and the given scheme pairing on every test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction

theorem exists_stable_self_annihilating_unmarked_subgroup_parameter
    {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom]
    (n : ℕ) (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x))
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    {I : Type*} [Finite I] (a : I → (A ⟶ A)) [∀ i, IsMonHom (a i)]
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n)
      (B := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) :
    ∃ (Q : Over S) (U : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice A n M Q),
      IsFinite Q.hom ∧ Etale Q.hom ∧
      (∀ i, SubgroupStability.RelativeSubgroupStable U.subgroup (a i)) ∧
      (let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) U.subgroup
       e.relativeAnnihilator H = H) ∧
      ∀ (T : Over S) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice A n M T),
        ((∀ i, SubgroupStability.RelativeSubgroupStable F.subgroup (a i)) ∧
          (let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) F.subgroup
           e.relativeAnnihilator H = H)) ↔
          ∃! f : T ⟶ Q, U.baseChange f = F := by
  obtain ⟨P, U, hPf, hPe, hstable, hclass⟩ :=
    StableUnmarkedSubgroups.exists_finite_etale_stable_unmarked_subgroup_parameter A n hn M a
  let : IsFinite P.hom := hPf
  let : Etale P.hom := hPe
  have htor := AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale A n hn
  have hnative := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme_finite_etale A n htor
  let : IsFinite (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n).hom := hnative.1
  let : Etale (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n).hom := hnative.2
  let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) U.subgroup
  let R : H.Model := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.torsionRelativeSubgroup_model n U.subgroup U.geometric.some U.killed
  obtain ⟨Q, j, hjo, hjc, hQ⟩ := SelfAnnihilatingSubgroupParameter.exists_self_annihilating_subgroup_parameter
    e n (AbelianScheme.IsogenyQuotient.Torsion.PairingTarget.Construction.nativeTorsionScheme_identity_killed A n) hn H R
  let : IsOpenImmersion j.left := hjo
  let : IsClosedImmersion j.left := hjc
  let : Mono j := Over.mono_of_mono_left j
  have hQf : IsFinite Q.hom := by
    rw [← j.w]
    infer_instance
  have hQe : Etale Q.hom := by
    rw [← j.w]
    infer_instance
  have hjs : ∀ i, SubgroupStability.RelativeSubgroupStable (U.baseChange j).subgroup (a i) :=
    fun i => SubgroupStability.relativeSubgroupStable_baseChange (a i) (hstable i) j
  have hjlag : e.relativeAnnihilator (H.baseChange j) = H.baseChange j := by
    apply (hQ Q j).mp
    exact ⟨𝟙 Q, Category.id_comp _,
      fun k hk => (cancel_mono j).mp (hk.trans (Category.id_comp _).symm)⟩
  refine ⟨Q, U.baseChange j, hQf, hQe, hjs, hjlag, ?_⟩
  intro T F
  constructor
  · rintro ⟨hFs, hFl⟩
    obtain ⟨f, hf, huniq⟩ := (hclass T F).mp hFs
    have hfl : e.relativeAnnihilator (H.baseChange f) = H.baseChange f := by
      change e.relativeAnnihilator
        (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) (U.baseChange f).subgroup) =
        AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) (U.baseChange f).subgroup
      rw [hf]
      exact hFl
    obtain ⟨k, hk, hkuniq⟩ := (hQ T f).mpr hfl
    have hUk : (U.baseChange j).baseChange k = F :=
      (U.baseChange_comp j k).symm.trans ((congrArg U.baseChange hk).trans hf)
    refine ⟨k, hUk, ?_⟩
    intro k' hk'
    apply hkuniq
    apply huniq
    rw [U.baseChange_comp j k', hk']
  · rintro ⟨f, hf, _⟩
    constructor
    · intro i
      have h := SubgroupStability.relativeSubgroupStable_baseChange (a i) (hjs i) f
      change SubgroupStability.RelativeSubgroupStable ((U.baseChange j).baseChange f).subgroup (a i) at h
      exact hf ▸ h
    · have hl := congrArg (fun G => G.baseChange f) hjlag
      rw [e.relativeAnnihilator_baseChange] at hl
      change e.relativeAnnihilator
        (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n)
          ((U.baseChange j).baseChange f).subgroup) =
        AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n)
          ((U.baseChange j).baseChange f).subgroup at hl
      rwa [hf] at hl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableIsotropicSubgroupParameter
