import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.UniversalUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupMarkingCover
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupDetection
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.OverDescentUnique

/-! # Classifying Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.ClassifyingMap.UniversalSubgroup

/-! Constructing the unique classifying map of an actual finite subgroup family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H T : Over S} [GrpObj H]
variable {M : Type u} [Group M] [Fintype M]
variable [IsFinite H.hom] [Etale H.hom]
variable (D : Unmarked.UnmarkedQuotient.Data H M) {F : SubgroupFunctor.RelativeSubgroup H T} (R : F.Model)

theorem exists_descended_marking (hType : SubgroupMarkingCover.SubgroupMarkingLocus.HasType F M) :
    ∃ f : T ⟶ D.parameter,
      SubgroupMarkingIs.SubgroupMarkingLocus.toBase (M := M) R ≫ f =
        SubgroupMarkingIs.SubgroupMarkingLocus.marking R ≫ D.projection := by
  have : Etale D.parameter.hom := D.etale
  obtain ⟨hf, he⟩ := SubgroupMarkingIs.SubgroupMarkingLocus.finite_etale (M := M) R
  let : IsFinite (SubgroupMarkingIs.SubgroupMarkingLocus.toBase (M := M) R).left := hf
  let : Etale (SubgroupMarkingIs.SubgroupMarkingLocus.toBase (M := M) R).left := he
  let : Surjective (SubgroupMarkingIs.SubgroupMarkingLocus.toBase (M := M) R).left :=
    SubgroupMarkingCover.SubgroupMarkingLocus.surjective R hType
  have hi : ∀ (U : Over S) (a b : U ⟶ SubgroupMarkingIs.SubgroupMarkingLocus.carrier (M := M) R),
      a ≫ SubgroupMarkingIs.SubgroupMarkingLocus.toBase R = b ≫ SubgroupMarkingIs.SubgroupMarkingLocus.toBase R →
      a ≫ (SubgroupMarkingIs.SubgroupMarkingLocus.marking R ≫ D.projection) =
        b ≫ (SubgroupMarkingIs.SubgroupMarkingLocus.marking R ≫ D.projection) := by
    intro U a b hab
    apply IsogenyQuotient.Geometric.Points.Construction.etale_ext_of_geometric_points
    intro K hK hclosed s x
    have hb : (x ≫ a) ≫ SubgroupMarkingIs.SubgroupMarkingLocus.toBase R =
        (x ≫ b) ≫ SubgroupMarkingIs.SubgroupMarkingLocus.toBase R := by
      simpa only [Category.assoc] using congrArg (fun f => x ≫ f) hab
    have ha' := SubgroupMarkingCover.SubgroupMarkingLocus.geometric_range R hType K s (x ≫ a)
    have hb' := SubgroupMarkingCover.SubgroupMarkingLocus.geometric_range R hType K s (x ≫ b)
    have hr := ha'.trans ((congrArg (F.points (Over.mk s)) hb).trans hb'.symm)
    have hp := (MarkingRangesIff.MarkingRanges.same_projection_iff_range D K s
      ((x ≫ a) ≫ SubgroupMarkingIs.SubgroupMarkingLocus.marking R)
      ((x ≫ b) ≫ SubgroupMarkingIs.SubgroupMarkingLocus.marking R)).mpr hr
    simpa only [Category.assoc] using hp
  obtain ⟨f, hf, _⟩ := OverDescentUnique.OverDescent.existsUnique (SubgroupMarkingIs.SubgroupMarkingLocus.toBase R)
    (SubgroupMarkingIs.SubgroupMarkingLocus.marking R ≫ D.projection) hi
  exact ⟨f, hf⟩

include R in
theorem exists_classifying (hType : SubgroupMarkingCover.SubgroupMarkingLocus.HasType F M) :
    ∃ f : T ⟶ D.parameter, (UniversalSubgroupEq.UniversalSubgroup.subgroup D).baseChange f = F := by
  obtain ⟨f, hf⟩ := exists_descended_marking D R hType
  refine ⟨f, ?_⟩
  apply SubgroupDetection.EtaleSubgroupModels.eq_of_geometric_points ((UniversalSubgroupEq.UniversalSubgroup.model D).baseChange f) R
  intro K hK hclosed s t
  change (UniversalSubgroupEq.UniversalSubgroup.subgroup D).points (Over.mk s) (t ≫ f) = F.points (Over.mk s) t
  rw [UniversalSubgroupEq.UniversalSubgroup.geometric_points_eq]
  obtain ⟨z, hz⟩ := SubgroupMarkingCover.SubgroupMarkingLocus.geometric_lift R hType K s t
  have hr := SubgroupMarkingCover.SubgroupMarkingLocus.geometric_range R hType K s z
  rw [hz] at hr
  have hp : (z ≫ SubgroupMarkingIs.SubgroupMarkingLocus.marking R) ≫ D.projection = t ≫ f := by
    calc
      _ = z ≫ (SubgroupMarkingIs.SubgroupMarkingLocus.marking R ≫ D.projection) := Category.assoc _ _ _
      _ = z ≫ (SubgroupMarkingIs.SubgroupMarkingLocus.toBase R ≫ f) := congrArg (fun a => z ≫ a) hf.symm
      _ = (z ≫ SubgroupMarkingIs.SubgroupMarkingLocus.toBase R) ≫ f := (Category.assoc _ _ _).symm
      _ = t ≫ f := congrArg (fun a => a ≫ f) hz
  have he := (MarkingRangesIff.MarkingRanges.same_projection_iff_range D K s
    (z ≫ SubgroupMarkingIs.SubgroupMarkingLocus.marking R) (UniversalSubgroupEq.UniversalSubgroup.geometricMark D K s (t ≫ f))).mp
      (hp.trans (UniversalSubgroupEq.UniversalSubgroup.geometricMark_projection D K s (t ≫ f)).symm)
  exact he.symm.trans hr

include R in
/-- Every genuine finite flat subgroup family of the prescribed geometric
type is the pullback of the constructed universal subgroup along one and
only one morphism. -/
theorem existsUnique_classifying (hType : SubgroupMarkingCover.SubgroupMarkingLocus.HasType F M) :
    ∃! f : T ⟶ D.parameter, (UniversalSubgroupEq.UniversalSubgroup.subgroup D).baseChange f = F := by
  obtain ⟨f, hf⟩ := exists_classifying D R hType
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact UniversalUniqueness.UniversalSubgroup.classifying_injective D g f (hg.trans hf.symm)

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.ClassifyingMap.UniversalSubgroup
