import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.ClassifyingMap
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Subgroups
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale

/-! # Representability And -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.RepresentabilityAnd

/-!
# TorsionQuotient: representability of the original unmarked torsion-subgroup functor

The parameter is the constructed finite étale quotient of the marking
scheme. The universal subgroup is an actual finite étale incidence scheme,
and arbitrary families are classified by descent from their marking covers.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Representability

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)
variable (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
variable [IsFinite (SubgroupFunctor.torsionScheme A n).hom] [Etale (SubgroupFunctor.torsionScheme A n).hom]

noncomputable local instance : Fintype (Multiplicative M) := Fintype.ofFinite _

noncomputable abbrev data : Unmarked.UnmarkedQuotient.Data (SubgroupFunctor.torsionScheme A n) (Multiplicative M) :=
  Unmarked.UnmarkedQuotient.constructed (SubgroupFunctor.torsionScheme A n) (Multiplicative M)

noncomputable abbrev parameter : Over S := (data A n M).parameter

noncomputable def universal : SubgroupFunctor.SubgroupChoice A n M (Representability.parameter A n M) where
  subgroup := Subgroups.TorsionSubgroups.extend A n (UniversalSubgroupEq.UniversalSubgroup.subgroup (data A n M))
  killed := Subgroups.TorsionSubgroups.extend_killed A n _
  moduleType := by
    intro K hK hclosed s t
    exact ⟨(SubgroupTransferIff.SubgroupTransfer.pointsEquiv (SubgroupFunctor.torsionι A n)
      (UniversalSubgroupEq.UniversalSubgroup.subgroup (data A n M)) (Over.mk s) t).symm.trans
        (UniversalSubgroupEq.UniversalSubgroup.geometricType (data A n M) K s t)⟩
  geometric := ⟨SubgroupTransferIff.SubgroupTransfer.mapModel (SubgroupFunctor.torsionι A n)
    (UniversalSubgroupEq.UniversalSubgroup.model (data A n M))⟩

noncomputable def points (T : Over S) (f : T ⟶ Representability.parameter A n M) : SubgroupFunctor.SubgroupChoice A n M T :=
  (universal A n M).baseChange f

theorem points_injective (T : Over S) : Function.Injective (points A n M T) := by
  intro f g h
  have he := congrArg SubgroupFunctor.SubgroupChoice.subgroup h
  change (SubgroupTransferIff.SubgroupTransfer.map (SubgroupFunctor.torsionι A n) (UniversalSubgroupEq.UniversalSubgroup.subgroup (data A n M))).baseChange f =
    (SubgroupTransferIff.SubgroupTransfer.map (SubgroupFunctor.torsionι A n) (UniversalSubgroupEq.UniversalSubgroup.subgroup (data A n M))).baseChange g at he
  rw [SubgroupTransferIff.SubgroupTransfer.map_baseChange, SubgroupTransferIff.SubgroupTransfer.map_baseChange] at he
  have hr := congrArg (SubgroupTransferIff.SubgroupTransfer.comap (SubgroupFunctor.torsionι A n)) he
  rw [SubgroupTransferIff.SubgroupTransfer.comap_map, SubgroupTransferIff.SubgroupTransfer.comap_map] at hr
  exact UniversalUniqueness.UniversalSubgroup.classifying_injective (data A n M) f g hr

theorem points_surjective (T : Over S) : Function.Surjective (points A n M T) := by
  intro F
  let R := F.geometric.some
  let G := Subgroups.TorsionSubgroups.restrict A n F.subgroup
  let RG := Subgroups.TorsionSubgroups.restrictModel A n R F.killed
  have hType : SubgroupMarkingCover.SubgroupMarkingLocus.HasType G (Multiplicative M) := by
    intro K hK hclosed s t
    obtain ⟨e⟩ := F.moduleType K s t
    exact ⟨(Subgroups.TorsionSubgroups.restrictPointsEquiv A n F.subgroup F.killed (Over.mk s) t).trans e⟩
  obtain ⟨f, hf⟩ := ClassifyingMap.UniversalSubgroup.exists_classifying (data A n M) RG hType
  refine ⟨f, ?_⟩
  apply SubgroupFunctor.SubgroupChoice.ext
  change (SubgroupTransferIff.SubgroupTransfer.map (SubgroupFunctor.torsionι A n) (UniversalSubgroupEq.UniversalSubgroup.subgroup (data A n M))).baseChange f =
    F.subgroup
  rw [SubgroupTransferIff.SubgroupTransfer.map_baseChange, hf]
  exact Subgroups.TorsionSubgroups.extend_restrict A n F.subgroup F.killed

noncomputable def representable : (SubgroupFunctor.subgroupChoiceFunctor A n M).RepresentableBy (Representability.parameter A n M) where
  homEquiv := Equiv.ofBijective (points A n M _) ⟨points_injective A n M _, points_surjective A n M _⟩
  homEquiv_comp f g := (universal A n M).baseChange_comp g f

theorem finite_etale_parameter :
    IsFinite (Representability.parameter A n M).hom ∧ Etale (Representability.parameter A n M).hom ∧
      Nonempty (uliftYoneda.{u + 1}.obj (Representability.parameter A n M) ≅ SubgroupFunctor.subgroupChoiceFunctor A n M) :=
  ⟨(data A n M).finite, (data A n M).etale,
    ⟨Functor.RepresentableBy.equivUliftYonedaIso (SubgroupFunctor.subgroupChoiceFunctor A n M)
      (Representability.parameter A n M) (representable A n M)⟩⟩

end Representability

namespace Construction

/-- Prime-to-residue-characteristic torsion of a smooth proper commutative
group scheme, and the parameter spaces for its actual finite subgroups of
any fixed finite module type, are finite étale. -/
theorem finite_etale_torsion_and_subgroup_parameters
    {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom]
    (n : ℕ) (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s))
    (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M] :
    IsFinite (SubgroupFunctor.torsionScheme A n).hom ∧ Etale (SubgroupFunctor.torsionScheme A n).hom ∧
      ∃ P : Over S, IsFinite P.hom ∧ Etale P.hom ∧
        Nonempty (uliftYoneda.{u + 1}.obj P ≅ SubgroupFunctor.subgroupChoiceFunctor A n M) := by
  obtain ⟨hf, he⟩ := TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale A n hn
  let := hf
  let := he
  exact ⟨hf, he, Representability.parameter A n M, Representability.finite_etale_parameter A n M⟩

end Construction

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.RepresentabilityAnd
