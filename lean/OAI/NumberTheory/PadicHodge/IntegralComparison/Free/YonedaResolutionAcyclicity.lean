import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationSheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Acyclicity

/-! # Yoneda Resolution Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaResolutionAcyclicity

noncomputable section

/-! Exact sections of an actual injective resolution compute the
vanishing of Ext from the original free representable sheaf. -/

open _root_.CategoryTheory Opposite

universe u v z
variable {C : Type (max u v)} [Category.{v} C]
  (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasSheafify J (ModuleCat.{max u v} R)]
  [HasExt.{z} (Sheaf J (ModuleCat.{max u v} R))]
  (U : C) {M : Sheaf J (ModuleCat.{max u v} R)} (I : InjectiveResolution M)

theorem subsingleton (n : ℕ)
    (h : ∀ x : (I.cocomplex.X (n + 1)).obj.obj (op U),
      (I.cocomplex.d (n + 1) (n + 2)).hom.app (op U) x = 0 →
        ∃ y : (I.cocomplex.X n).obj.obj (op U),
          (I.cocomplex.d n (n + 1)).hom.app (op U) y = x) :
    Subsingleton (Abelian.Ext.{z} (Sheaf.freeYoneda J U (ModuleCat.of R R)) M (n + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (n + 2) rfl
  let e := fun i => PresentationSheafSections.freeSections R J U (I.cocomplex.X i)
  have hx : (I.cocomplex.d (n + 1) (n + 2)).hom.app (op U) (e (n + 1) a) = 0 := by
    rw [← PresentationSheafSections.freeSections_natural, ha, AddEquiv.map_zero]
  obtain ⟨y, hy⟩ := h (e (n + 1) a) hx
  apply (I.extMk_eq_zero_iff a (n + 2) rfl ha n rfl).mpr
  refine ⟨(e n).symm y, ?_⟩
  apply (e (n + 1)).injective
  rw [PresentationSheafSections.freeSections_natural]
  change (I.cocomplex.d n (n + 1)).hom.app (op U) (e n ((e n).symm y)) = _
  rw [AddEquiv.apply_symm_apply]
  exact hy

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaResolutionAcyclicity
