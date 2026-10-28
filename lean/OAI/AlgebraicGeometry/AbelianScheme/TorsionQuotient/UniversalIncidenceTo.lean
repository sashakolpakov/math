import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.MarkingRangesIff
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteEtaleIff

/-! # Universal Incidence To -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.UniversalIncidenceTo.UniversalIncidence

/-! The actual finite étale incidence scheme over the unmarked parameter. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
variable {M : Type u} [Group M] [Fintype M]
variable [IsFinite H.hom] [Etale H.hom] (D : Unmarked.UnmarkedQuotient.Data H M)

local instance : IsFinite D.parameter.hom := D.finite
local instance : Etale D.parameter.hom := D.etale

noncomputable abbrev labels : Over S :=
  FreeConstant.FreeConstantAction.relation (X := EmbeddingParametersIs.EmbeddingParameters.parameter H M) (G := M)

noncomputable abbrev ambient : Over S := D.parameter ⨯ H

theorem ambient_finite_etale : IsFinite (ambient D).hom ∧ Etale (ambient D).hom := by
  apply FiniteEtaleLift.FiniteEtaleLimits.finite_limit (pair D.parameter H)
  rintro ⟨j⟩
  cases j
  · exact show FiniteEtaleLift.FiniteEtaleLimits.property D.parameter.hom from ⟨inferInstance, inferInstance⟩
  · exact show FiniteEtaleLift.FiniteEtaleLimits.property H.hom from ⟨inferInstance, inferInstance⟩

local instance : IsFinite (ambient D).hom := (ambient_finite_etale D).1
local instance : Etale (ambient D).hom := (ambient_finite_etale D).2

noncomputable def coefficient (m : M) : EmbeddingParametersIs.EmbeddingParameters.parameter H M ⟶ H :=
  (EmbeddingParametersIs.EmbeddingParameters.points H M _ (𝟙 _)).val m

noncomputable def evaluation : labels (H := H) (M := M) ⟶ H :=
  Over.homMk (Sigma.desc (fun m => (coefficient (H := H) m).left)) (by
    change (Sigma.desc (fun m => (coefficient (H := H) m).left)) ≫ H.hom =
      (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (EmbeddingParametersIs.EmbeddingParameters.parameter H M).left M).hom ≫
        (EmbeddingParametersIs.EmbeddingParameters.parameter H M).hom
    apply Sigma.hom_ext
    intro m
    rw [Sigma.ι_comp_desc_assoc]
    exact (coefficient (H := H) m).w.trans (FreeConstant.FreeConstantAction.inclusion m).w.symm)

@[simp, reassoc]
theorem inclusion_evaluation (m : M) : FreeConstant.FreeConstantAction.inclusion m ≫
    evaluation (H := H) = coefficient (H := H) m :=
  Over.OverMorphism.ext (Sigma.ι_comp_desc _ _)

theorem comp_coefficient {T : Over S} (a : T ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M) (m : M) :
    a ≫ coefficient (H := H) m = (EmbeddingParametersIs.EmbeddingParameters.points H M T a).val m := by
  change a ≫ ((𝟙 _ ≫ EmbeddingParametersIs.EmbeddingParameters.inclusion H M) ≫ HomParametersMul.HomParameters.coefficient H M m) =
    (a ≫ EmbeddingParametersIs.EmbeddingParameters.inclusion H M) ≫ HomParametersMul.HomParameters.coefficient H M m
  simp only [Category.id_comp, Category.assoc]

noncomputable def incidenceMap : labels (H := H) (M := M) ⟶ ambient D :=
  prod.lift (FreeConstant.FreeConstantAction.source ≫ D.projection) evaluation

noncomputable abbrev carrier : Over S := FiniteEtaleIff.FiniteEtaleImage.image (incidenceMap D)

noncomputable abbrev inclusion : carrier D ⟶ ambient D :=
  FiniteEtaleIff.FiniteEtaleImage.inclusion (incidenceMap D)

noncomputable def toBase : carrier D ⟶ D.parameter := inclusion D ≫ prod.fst

noncomputable def toGroup : carrier D ⟶ H := inclusion D ≫ prod.snd

theorem finite_etale : IsFinite (toBase D).left ∧ Etale (toBase D).left :=
  FiniteEtaleLift.FiniteEtaleLimits.hom_finite_etale (toBase D)

theorem jointly_monic {T : Over S} (a b : T ⟶ carrier D)
    (hb : a ≫ toBase D = b ≫ toBase D) (hg : a ≫ toGroup D = b ≫ toGroup D) : a = b := by
  apply (cancel_mono (inclusion D)).mp
  apply prod.hom_ext
  · exact (Category.assoc _ _ _).trans (hb.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (hg.trans (Category.assoc _ _ _).symm)

theorem factors_iff {T : Over S} (t : T ⟶ D.parameter) (a : T ⟶ H) :
    (∃ h : T ⟶ carrier D, h ≫ toBase D = t ∧ h ≫ toGroup D = a) ↔
      ∃ h : T ⟶ carrier D, h ≫ inclusion D = prod.lift t a := by
  constructor
  · rintro ⟨h, hb, hg⟩
    refine ⟨h, ?_⟩
    apply prod.hom_ext
    · exact (Category.assoc _ _ _).trans (hb.trans (prod.lift_fst t a).symm)
    · exact (Category.assoc _ _ _).trans (hg.trans (prod.lift_snd t a).symm)
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_, ?_⟩
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ prod.fst) hh).trans (prod.lift_fst t a))
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ prod.snd) hh).trans (prod.lift_snd t a))

theorem geometric_points (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ D.parameter) (a : Over.mk s ⟶ H) :
    (∃ h : Over.mk s ⟶ carrier D, h ≫ toBase D = t ∧ h ≫ toGroup D = a) ↔
      ∃ (e : Over.mk s ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M) (m : M),
        e ≫ D.projection = t ∧ (EmbeddingParametersIs.EmbeddingParameters.points H M _ e).val m = a := by
  rw [factors_iff, FiniteEtaleIff.FiniteEtaleImage.geometric_factors_iff]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨m, hm⟩ := FreeConstant.FreeConstantAction.field_factor K s x
    refine ⟨x ≫ FreeConstant.FreeConstantAction.source, m, ?_, ?_⟩
    · have he := congrArg (fun f => f ≫ prod.fst) hx
      simpa only [incidenceMap, Category.assoc, prod.lift_fst] using he
    · have he := congrArg (fun f => f ≫ prod.snd) hx
      have he' : x ≫ evaluation = a := by
        simpa only [incidenceMap, Category.assoc, prod.lift_snd] using he
      have hm' := congrArg (fun f => f ≫ evaluation (H := H)) hm
      rw [Category.assoc, inclusion_evaluation, comp_coefficient, he'] at hm'
      exact hm'.symm
  · rintro ⟨e, m, he, hm⟩
    refine ⟨e ≫ FreeConstant.FreeConstantAction.inclusion m, ?_⟩
    apply prod.hom_ext
    · simp only [incidenceMap, Category.assoc, prod.lift_fst,
        FreeConstant.FreeConstantAction.inclusion_source_assoc]
      exact he
    · simp only [incidenceMap, Category.assoc, prod.lift_snd, inclusion_evaluation]
      exact (comp_coefficient e m).trans hm

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.UniversalIncidenceTo.UniversalIncidence
