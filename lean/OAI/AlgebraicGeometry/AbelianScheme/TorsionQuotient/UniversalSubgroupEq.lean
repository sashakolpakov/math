import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.UniversalIncidenceTo

/-! # Universal Subgroup Eq -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup

/-! The finite étale incidence scheme represents an actual subgroup family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
variable {M : Type u} [Group M] [Fintype M]
variable [IsFinite H.hom] [Etale H.hom] (D : Unmarked.UnmarkedQuotient.Data H M)

local instance : IsFinite (UniversalIncidenceTo.UniversalIncidence.ambient D).hom :=
  (UniversalIncidenceTo.UniversalIncidence.ambient_finite_etale D).1
local instance : Etale (UniversalIncidenceTo.UniversalIncidence.ambient D).hom :=
  (UniversalIncidenceTo.UniversalIncidence.ambient_finite_etale D).2

noncomputable def geometricMark (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ D.parameter) :
    Over.mk s ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M :=
  (Points.UnmarkedQuotient.geometric_surjective D K s t).choose

theorem geometricMark_projection (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ D.parameter) :
    geometricMark D K s t ≫ D.projection = t :=
  (Points.UnmarkedQuotient.geometric_surjective D K s t).choose_spec

noncomputable def geometricGroup (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ D.parameter) :
    Subgroup (Over.mk s ⟶ H) :=
  (EmbeddingParametersIs.EmbeddingParameters.points H M _ (geometricMark D K s t)).val.range

theorem geometric_iff (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ D.parameter) (a : Over.mk s ⟶ H) :
    a ∈ geometricGroup D K s t ↔
      ∃ h : Over.mk s ⟶ UniversalIncidenceTo.UniversalIncidence.carrier D,
        h ≫ UniversalIncidenceTo.UniversalIncidence.toBase D = t ∧ h ≫ UniversalIncidenceTo.UniversalIncidence.toGroup D = a := by
  rw [UniversalIncidenceTo.UniversalIncidence.geometric_points]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨geometricMark D K s t, m, geometricMark_projection D K s t, hm⟩
  · rintro ⟨e, m, he, hm⟩
    have hr := (MarkingRangesIff.MarkingRanges.same_projection_iff_range D K s e (geometricMark D K s t)).mp
      (he.trans (geometricMark_projection D K s t).symm)
    change a ∈ (EmbeddingParametersIs.EmbeddingParameters.points H M _ (geometricMark D K s t)).val.range
    rw [← hr]
    exact ⟨m, hm⟩

noncomputable def subgroup : SubgroupFunctor.RelativeSubgroup H D.parameter where
  points T t :=
    { carrier := {a | ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk s ⟶ T),
        x ≫ a ∈ geometricGroup D K s (x ≫ t)}
      one_mem' := by
        intro K hK hclosed s x
        rw [MonObj.comp_one]
        exact (geometricGroup D K s (x ≫ t)).one_mem
      mul_mem' := by
        intro a b ha hb K hK hclosed s x
        rw [MonObj.comp_mul]
        exact (geometricGroup D K s (x ≫ t)).mul_mem (ha K s x) (hb K s x)
      inv_mem' := by
        intro a ha K hK hclosed s x
        rw [GrpObj.comp_inv]
        exact (geometricGroup D K s (x ≫ t)).inv_mem (ha K s x) }
  naturality := by
    intro T U f t a ha K hK hclosed s x
    have h := ha K s (x ≫ f)
    simpa only [Category.assoc] using h

/-- The actual incidence scheme represents the family on all test schemes. -/
theorem membership_iff {T : Over S} (t : T ⟶ D.parameter) (a : T ⟶ H) :
    a ∈ (subgroup D).points T t ↔
      ∃ h : T ⟶ UniversalIncidenceTo.UniversalIncidence.carrier D,
        h ≫ UniversalIncidenceTo.UniversalIncidence.toBase D = t ∧ h ≫ UniversalIncidenceTo.UniversalIncidence.toGroup D = a := by
  constructor
  · intro ha
    apply (UniversalIncidenceTo.UniversalIncidence.factors_iff D t a).mpr
    apply (FiniteEtaleIff.FiniteEtaleImage.factors_iff_geometric (UniversalIncidenceTo.UniversalIncidence.incidenceMap D)
      (prod.lift t a)).mpr
    intro K hK hclosed s x
    obtain ⟨h, hb, hg⟩ := (geometric_iff D K s (x ≫ t) (x ≫ a)).mp (ha K s x)
    obtain ⟨h', hh'⟩ := (UniversalIncidenceTo.UniversalIncidence.factors_iff D (x ≫ t) (x ≫ a)).mp ⟨h, hb, hg⟩
    exact ⟨h', hh'.trans (prod.comp_lift x t a).symm⟩
  · rintro ⟨h, hb, hg⟩ K hK hclosed s x
    apply (geometric_iff D K s (x ≫ t) (x ≫ a)).mpr
    refine ⟨x ≫ h, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans (congrArg (fun f => x ≫ f) hb)
    · exact (Category.assoc _ _ _).trans (congrArg (fun f => x ≫ f) hg)

noncomputable def model : (subgroup D).Model where
  carrier := UniversalIncidenceTo.UniversalIncidence.carrier D
  toBase := UniversalIncidenceTo.UniversalIncidence.toBase D
  toGroup := UniversalIncidenceTo.UniversalIncidence.toGroup D
  finite := (UniversalIncidenceTo.UniversalIncidence.finite_etale D).1
  flat := by
    have : Etale (UniversalIncidenceTo.UniversalIncidence.toBase D).left := (UniversalIncidenceTo.UniversalIncidence.finite_etale D).2
    infer_instance
  finitePresentation := by
    have : Etale (UniversalIncidenceTo.UniversalIncidence.toBase D).left := (UniversalIncidenceTo.UniversalIncidence.finite_etale D).2
    infer_instance
  jointly_monic := fun _ a b => UniversalIncidenceTo.UniversalIncidence.jointly_monic D a b
  points_iff := fun _ t a => membership_iff D t a

theorem geometric_points_eq (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ D.parameter) :
    (subgroup D).points (Over.mk s) t = geometricGroup D K s t := by
  apply Subgroup.ext
  intro a
  exact (membership_iff D t a).trans (geometric_iff D K s t a).symm

noncomputable def geometricType (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ D.parameter) :
    (subgroup D).points (Over.mk s) t ≃* M := by
  let e := geometricMark D K s t
  have hi : Function.Injective (EmbeddingParametersIs.EmbeddingParameters.points H M _ e).val := by
    intro m n h
    apply (EmbeddingParametersIs.EmbeddingParameters.points H M _ e).property K s (𝟙 _)
    simpa only [Category.id_comp] using h
  exact (MulEquiv.subgroupCongr (geometric_points_eq D K s t)).trans
    (MonoidHom.ofInjective hi).symm

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.UniversalSubgroupEq.UniversalSubgroup
