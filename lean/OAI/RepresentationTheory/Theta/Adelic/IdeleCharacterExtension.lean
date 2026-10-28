import OAI.RepresentationTheory.Theta.Adelic.IdeleClassEmbedding
import OAI.Topology.Pontryagin.CharacterExtension

/-! # Idele Character Extension -/

namespace OAI.RepresentationTheory.Theta.Adelic.IdeleCharacterExtension

noncomputable section

/-! Character extension on the concrete base and quadratic idele classes,
using the proved closed embedding and the checked Pontryagin theorem. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection
open OAI.RepresentationTheory.Theta.Adelic.IdeleClassEmbedding OAI.RepresentationTheory.Theta.Adelic.RationalClosed

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d)

include hd hns in
theorem extend_ideleClass_character (χ : NumberTheory.Adeles.LocalCompletions.CompletionFactors.IdeleClass F →ₜ* Circle) :
    ∃ χE : IdeleClassInjection.QuadraticIdeleClass F d →ₜ* Circle,
      ∀ x, χE (IdeleClassInjection.scalarIdeleClass F d x) = χ x := by
  let : IsClosed ((IdeleClassInjection.quadraticPrincipal F d).range : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) :=
    IdeleClassEmbedding.quadraticPrincipal_range_closed F d hns
  let : T2Space (IdeleClassInjection.QuadraticIdeleClass F d) := inferInstance
  let : LocallyCompactSpace (IdeleClassInjection.QuadraticIdeleClass F d) := inferInstance
  let f := (IdeleClassInjection.scalarIdeleClass F d).rangeRestrict
  have hs : Function.Surjective f := by
    rintro ⟨y, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩
  have hi : Function.Injective f := fun x y h =>
    IdeleClassInjection.scalarIdeleClass_injective F d (congrArg Subtype.val h)
  let e : NumberTheory.Adeles.LocalCompletions.CompletionFactors.IdeleClass F ≃* (IdeleClassInjection.scalarIdeleClass F d).range :=
    MulEquiv.ofBijective f ⟨hi, hs⟩
  have he : Topology.IsEmbedding e :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
      (IdeleClassEmbedding.scalarIdeleClass_closedEmbedding F d hd hns).isEmbedding
  have hei : Continuous e.symm := by
    apply he.continuous_iff.mpr
    change Continuous (fun x => e (e.symm x))
    have heq : (fun x => e (e.symm x)) = (id : (IdeleClassInjection.scalarIdeleClass F d).range → _) :=
      funext e.apply_symm_apply
    rw [heq]
    exact continuous_id
  let χH : (IdeleClassInjection.scalarIdeleClass F d).range →ₜ* Circle :=
    χ.comp { e.symm.toMonoidHom with continuous_toFun := hei }
  obtain ⟨χE, hχE⟩ := OAI.Topology.Pontryagin.CharacterExtension.Constructions.pontryagin_character_extension
    (G := IdeleClassInjection.QuadraticIdeleClass F d)
    (IdeleClassInjection.scalarIdeleClass F d).range
    (IdeleClassClosed.scalarIdeleClass_range_closed F d hd hns) χH
  refine ⟨χE, ?_⟩
  intro x
  have h := hχE (e x)
  change χE (IdeleClassInjection.scalarIdeleClass F d x) = χ (e.symm (e x)) at h
  simpa only [e.symm_apply_apply] using h

include hd hns in
theorem extend_to_quadratic_Hecke_character (χ : NumberTheory.Adeles.LocalCompletions.CompletionFactors.IdeleClass F →ₜ* Circle) :
    ∃ χE : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →ₜ* Circle,
      (∀ a : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ, χE (IdeleClassInjection.quadraticPrincipal F d a) = 1) ∧
      ∀ x : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ,
        χE (IdeleClassInjection.scalarIdele F d x) = χ (QuotientGroup.mk' (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F).range x) := by
  obtain ⟨χC, hχC⟩ := extend_ideleClass_character F d hd hns χ
  let q : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →ₜ* IdeleClassInjection.QuadraticIdeleClass F d :=
    { QuotientGroup.mk' (IdeleClassInjection.quadraticPrincipal F d).range with
      continuous_toFun := QuotientGroup.continuous_mk }
  refine ⟨χC.comp q, ?_, ?_⟩
  · intro a
    have h : q (IdeleClassInjection.quadraticPrincipal F d a) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
    change χC (q (IdeleClassInjection.quadraticPrincipal F d a)) = 1
    rw [h, map_one]
  · intro x
    exact hχC (QuotientGroup.mk' (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F).range x)

end

end OAI.RepresentationTheory.Theta.Adelic.IdeleCharacterExtension
