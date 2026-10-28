import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleSubgroup
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.UniversalIncidenceTo

/-! # Subgroup Marking Is -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupMarkingIs.SubgroupMarkingLocus

/-! The finite étale locus of markings lying in a given subgroup family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H T : Over S} [GrpObj H]
variable {M : Type u} [Group M] [Fintype M]
variable [IsFinite H.hom] [Etale H.hom]
variable {F : SubgroupFunctor.RelativeSubgroup H T} (R : F.Model)

noncomputable abbrev ambient : Over S := T ⊗ EmbeddingParametersIs.EmbeddingParameters.parameter H M

noncomputable def evaluation (m : M) : ambient (T := T) (H := H) (M := M) ⟶ T ⊗ H :=
  lift (fst T _) (snd T _ ≫ UniversalIncidenceTo.UniversalIncidence.coefficient m)

noncomputable def support : Set (ambient (T := T) (H := H) (M := M)).left :=
  ⋂ m : M, (evaluation (T := T) (H := H) m).left ⁻¹'
    Set.range (EtaleSubgroup.EtaleSubgroupModels.inclusion R).left

theorem support_isClopen : IsClopen (support (M := M) R) :=
  isClopen_iInter_of_finite fun m =>
    ⟨(EtaleSubgroup.EtaleSubgroupModels.inclusion R).left.isClosedEmbedding.isClosed_range.preimage
        (evaluation (T := T) m).left.continuous,
      ((EtaleSubgroup.EtaleSubgroupModels.inclusion R).left.isOpenEmbedding.isOpen_range).preimage
        (evaluation (T := T) m).left.continuous⟩

noncomputable def locus : (ambient (T := T) (H := H) (M := M)).left.Opens :=
  ⟨support R, (support_isClopen R).isOpen⟩

noncomputable def carrier : Over S := Over.mk ((locus (M := M) R).ι ≫ (ambient (T := T) (H := H) (M := M)).hom)

noncomputable def inclusion : carrier (M := M) R ⟶ ambient (T := T) (H := H) (M := M) :=
  Over.homMk (locus R).ι rfl

instance inclusion_open : IsOpenImmersion (inclusion (M := M) R).left :=
  inferInstanceAs (IsOpenImmersion (locus R).ι)

instance inclusion_closed : IsClosedImmersion (inclusion (M := M) R).left := by
  apply IsClosedImmersion.of_isPreimmersion
  change IsClosed (Set.range (locus (M := M) R).ι)
  rw [Scheme.Opens.range_ι]
  exact (support_isClopen R).isClosed

noncomputable def toBase : carrier (M := M) R ⟶ T := inclusion R ≫ fst T _

noncomputable def marking : carrier (M := M) R ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M :=
  inclusion R ≫ snd T _

theorem finite_etale : IsFinite (toBase (M := M) R).left ∧ Etale (toBase (M := M) R).left := by
  have hf : IsFinite (fst T (EmbeddingParametersIs.EmbeddingParameters.parameter H M)).left :=
    inferInstanceAs (IsFinite (pullback.fst T.hom (EmbeddingParametersIs.EmbeddingParameters.parameter H M).hom))
  have he : Etale (fst T (EmbeddingParametersIs.EmbeddingParameters.parameter H M)).left :=
    inferInstanceAs (Etale (pullback.fst T.hom (EmbeddingParametersIs.EmbeddingParameters.parameter H M).hom))
  constructor
  · exact inferInstanceAs (IsFinite ((inclusion R).left ≫ (fst T _).left))
  · exact inferInstanceAs (Etale ((inclusion R).left ≫ (fst T _).left))

theorem inclusion_evaluation (m : M) : inclusion R ≫ evaluation (T := T) m =
    lift (toBase R) (marking R ≫ UniversalIncidenceTo.UniversalIncidence.coefficient m) := by
  apply hom_ext <;> simp only [evaluation, toBase, marking, comp_lift,
    Category.assoc, lift_fst, lift_snd]

theorem coefficient_mem (m : M) : marking R ≫ UniversalIncidenceTo.UniversalIncidence.coefficient m ∈
    F.points (carrier R) (toBase R) := by
  apply (EtaleSubgroup.EtaleSubgroupModels.membership_iff_range R _ _).mpr
  rintro _ ⟨x, rfl⟩
  have he := congrArg (fun f => f.left x) (inclusion_evaluation R m)
  rw [← he]
  exact Set.mem_iInter.mp x.property m

theorem exists_lift {V : Over S} (t : V ⟶ T) (c : V ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M)
    (hc : ∀ m : M, c ≫ UniversalIncidenceTo.UniversalIncidence.coefficient m ∈ F.points V t) :
    ∃ h : V ⟶ carrier (M := M) R, h ≫ toBase R = t ∧ h ≫ marking R = c := by
  let k := lift t c
  have hr : Set.range k.left ⊆ support R := by
    rintro _ ⟨x, rfl⟩
    apply Set.mem_iInter.mpr
    intro m
    have hm := (EtaleSubgroup.EtaleSubgroupModels.membership_iff_range R t
      (c ≫ UniversalIncidenceTo.UniversalIncidence.coefficient m)).mp (hc m)
    have he : k ≫ evaluation (T := T) m = lift t (c ≫ UniversalIncidenceTo.UniversalIncidence.coefficient m) := by
      apply hom_ext <;> simp only [k, evaluation, Category.assoc, lift_fst, lift_snd,
        lift_snd_assoc]
    exact hm ⟨x, (congrArg (fun f => f.left x) he).symm⟩
  have hr' : Set.range k.left ⊆ Set.range (locus (M := M) R).ι := by
    rw [Scheme.Opens.range_ι]
    exact hr
  let l := IsOpenImmersion.lift (locus R).ι k.left hr'
  have hl : l ≫ (locus R).ι = k.left := IsOpenImmersion.lift_fac _ _ _
  have hb : l ≫ (carrier (M := M) R).hom = V.hom := by
    change l ≫ ((locus R).ι ≫ (ambient (T := T) (H := H) (M := M)).hom) = V.hom
    rw [← Category.assoc, hl, k.w]
  let h : V ⟶ carrier R := Over.homMk l hb
  have hh : h ≫ inclusion R = k := Over.OverMorphism.ext hl
  refine ⟨h, ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ fst T _) hh).trans (lift_fst t c))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ snd T _) hh).trans (lift_snd t c))

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupMarkingIs.SubgroupMarkingLocus
