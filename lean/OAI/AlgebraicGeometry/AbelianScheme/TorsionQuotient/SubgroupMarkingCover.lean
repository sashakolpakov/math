import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupMarkingIs
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FieldMarkingsOf
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteSubgroup

/-! # Subgroup Marking Cover -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupMarkingCover.SubgroupMarkingLocus

/-! Every subgroup of the prescribed geometric type has a finite étale marking cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H T : Over S} [GrpObj H]
variable {M : Type u} [Group M] [Fintype M]
variable [IsFinite H.hom] [Etale H.hom]
variable {F : SubgroupFunctor.RelativeSubgroup H T} (R : F.Model)

def HasType (F : SubgroupFunctor.RelativeSubgroup H T) (M : Type u) [Group M] : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ T),
    Nonempty (F.points (Over.mk s) t ≃* M)

theorem geometric_range (hType : HasType F M) (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (z : Over.mk s ⟶ SubgroupMarkingIs.SubgroupMarkingLocus.carrier (M := M) R) :
    (EmbeddingParametersIs.EmbeddingParameters.points H M _ (z ≫ SubgroupMarkingIs.SubgroupMarkingLocus.marking R)).val.range =
      F.points (Over.mk s) (z ≫ SubgroupMarkingIs.SubgroupMarkingLocus.toBase R) := by
  obtain ⟨e⟩ := hType K s (z ≫ SubgroupMarkingIs.SubgroupMarkingLocus.toBase R)
  apply FiniteSubgroup.FiniteSubgroupRanges.range_eq_of_type _ _ _ _ e
  · intro m n h
    apply (EmbeddingParametersIs.EmbeddingParameters.points H M _ (z ≫ SubgroupMarkingIs.SubgroupMarkingLocus.marking R)).property K s (𝟙 _)
    simpa only [Category.id_comp] using h
  · intro m
    have hm := F.naturality z (SubgroupMarkingIs.SubgroupMarkingLocus.toBase R) (SubgroupMarkingIs.SubgroupMarkingLocus.coefficient_mem R m)
    rw [← Category.assoc, UniversalIncidenceTo.UniversalIncidence.comp_coefficient] at hm
    exact hm

theorem geometric_lift (hType : HasType F M) (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ T) :
    ∃ z : Over.mk s ⟶ SubgroupMarkingIs.SubgroupMarkingLocus.carrier (M := M) R, z ≫ SubgroupMarkingIs.SubgroupMarkingLocus.toBase R = t := by
  obtain ⟨e⟩ := hType K s t
  let a : M →* (Over.mk s ⟶ H) := (F.points (Over.mk s) t).subtype.comp e.symm.toMonoidHom
  have ha : Function.Injective a := Subtype.val_injective.comp e.symm.injective
  let c := FieldMarkingsOf.FieldMarkings.ofInjective K s a ha
  have hc : ∀ m : M, c ≫ UniversalIncidenceTo.UniversalIncidence.coefficient m ∈ F.points (Over.mk s) t := by
    intro m
    have hp : (EmbeddingParametersIs.EmbeddingParameters.points H M _ c).val = a :=
      FieldMarkingsOf.FieldMarkings.ofInjective_points K s a ha
    have hm : c ≫ UniversalIncidenceTo.UniversalIncidence.coefficient m = a m :=
      (UniversalIncidenceTo.UniversalIncidence.comp_coefficient c m).trans (congrArg (fun f => f m) hp)
    rw [hm]
    exact (e.symm m).property
  obtain ⟨z, hz, _⟩ := SubgroupMarkingIs.SubgroupMarkingLocus.exists_lift R t c hc
  exact ⟨z, hz⟩

theorem surjective (hType : HasType F M) : Surjective (SubgroupMarkingIs.SubgroupMarkingLocus.toBase (M := M) R).left := by
  constructor
  intro x
  let K := AlgebraicClosure (T.left.residueField x)
  let i := Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) K))
  let p := i ≫ T.left.fromSpecResidueField x
  let s := p ≫ T.hom
  let t : Over.mk s ⟶ T := Over.homMk p rfl
  obtain ⟨z, hz⟩ := geometric_lift R hType K s t
  let z₀ : Spec (CommRingCat.of K) := default
  refine ⟨z.left z₀, ?_⟩
  have he := congrArg (fun f => f.left z₀) hz
  exact he.trans (T.left.fromSpecResidueField_apply x (i z₀))

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupMarkingCover.SubgroupMarkingLocus
