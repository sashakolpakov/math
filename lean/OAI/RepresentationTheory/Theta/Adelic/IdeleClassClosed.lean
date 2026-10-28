import OAI.RepresentationTheory.Theta.Adelic.RationalClosed
import OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection
import OAI.RepresentationTheory.Theta.Adelic.QuadraticHilbert

/-! # Idele Class Closed -/

namespace OAI.RepresentationTheory.Theta.Adelic.IdeleClassClosed

noncomputable section

/-! The scalar idele-class image is closed. Its preimage in quadratic
ideles is characterized by rationality of a/star(a), using an explicit
quadratic Hilbert 90 calculation. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection
open OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection.ScalarFixed OAI.RepresentationTheory.Theta.Adelic.RationalClosed
open OAI.RepresentationTheory.Theta.Adelic.QuadraticHilbert

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d)

include hd hns in
theorem scalar_class_range_iff (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) :
    QuotientGroup.mk' (IdeleClassInjection.quadraticPrincipal F d).range a ∈ (IdeleClassInjection.scalarIdeleClass F d).range ↔
      (IdeleClassInjection.ScalarFixed.conjugationRatio F d a).val ∈ Set.range (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticRational F d) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    change QuotientGroup.mk' (IdeleClassInjection.quadraticPrincipal F d).range (IdeleClassInjection.scalarIdele F d x) =
      QuotientGroup.mk' (IdeleClassInjection.quadraticPrincipal F d).range a at hx
    obtain ⟨b, hb⟩ := QuotientGroup.eq_iff_div_mem.mp hx.symm
    have he := congrArg (IdeleClassInjection.ScalarFixed.conjugationRatio F d) hb
    rw [IdeleClassInjection.ScalarFixed.conjugationRatio_principal, (IdeleClassInjection.ScalarFixed.conjugationRatio F d).map_div,
      (IdeleClassInjection.ScalarFixed.conjugationRatio_eq_one_iff F d _).mpr ⟨x, rfl⟩, div_one] at he
    exact ⟨(b / star b).val, congrArg Units.val he⟩
  · rintro ⟨y, hy⟩
    let : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := ⟨by
      intro r hr
      apply hns
      exact ⟨r, by simpa only [zero_mul, add_zero, pow_two] using hr.symm⟩⟩
    have hy0 : y ≠ 0 := by
      intro h
      exact (IdeleClassInjection.ScalarFixed.conjugationRatio F d a).ne_zero (hy.symm.trans (h ▸ map_zero _))
    let u : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ := Units.mk0 y hy0
    have hu : IdeleClassInjection.quadraticPrincipal F d u = IdeleClassInjection.ScalarFixed.conjugationRatio F d a := Units.ext hy
    have hunorm : u * star u = 1 := by
      apply IdeleClassInjection.quadraticPrincipal_injective F d
      rw [map_mul, IdeleClassInjection.ScalarFixed.quadraticPrincipal_star, hu, map_one]
      exact IdeleClassInjection.ScalarFixed.conjugationRatio_norm_one F d a
    obtain ⟨b, hb⟩ := QuadraticHilbert.quadratic_hilbert90 d hd hns u hunorm
    have hr : IdeleClassInjection.ScalarFixed.conjugationRatio F d a = IdeleClassInjection.ScalarFixed.conjugationRatio F d (IdeleClassInjection.quadraticPrincipal F d b) := by
      rw [IdeleClassInjection.ScalarFixed.conjugationRatio_principal, hb, hu]
    have hk : IdeleClassInjection.ScalarFixed.conjugationRatio F d (a / IdeleClassInjection.quadraticPrincipal F d b) = 1 := by
      rw [map_div, hr]
      simp only [div_eq_mul_inv, mul_inv_cancel]
    obtain ⟨x, hx⟩ := (IdeleClassInjection.ScalarFixed.conjugationRatio_eq_one_iff F d _).mp hk
    refine ⟨QuotientGroup.mk' (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F).range x, ?_⟩
    change QuotientGroup.mk' (IdeleClassInjection.quadraticPrincipal F d).range (IdeleClassInjection.scalarIdele F d x) = _
    rw [hx, map_div]
    have hp : QuotientGroup.mk' (IdeleClassInjection.quadraticPrincipal F d).range (IdeleClassInjection.quadraticPrincipal F d b) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩
    rw [hp, div_one]

include hd hns in
theorem scalarIdeleClass_range_closed :
    IsClosed ((IdeleClassInjection.scalarIdeleClass F d).range : Set (IdeleClassInjection.QuadraticIdeleClass F d)) := by
  rw [← (QuotientGroup.isQuotientMap_mk (IdeleClassInjection.quadraticPrincipal F d).range).isClosed_preimage]
  have hc : Continuous (fun a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ => (IdeleClassInjection.ScalarFixed.conjugationRatio F d a).val) :=
    Units.continuous_val.comp (IdeleClassInjection.ScalarFixed.conjugationRatio_continuous F d)
  convert (RationalClosed.quadraticRational_range_closed F d).preimage hc using 1
  ext a
  exact scalar_class_range_iff F d hd hns a

end

end OAI.RepresentationTheory.Theta.Adelic.IdeleClassClosed
