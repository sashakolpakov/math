import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationLinearSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections

/-! # Yoneda Ext Zero Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaExtZeroEvaluation

noncomputable section

/-! The original free-representable degree-zero Ext functor is actual
evaluation, with the canonical coefficient universe lift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v z
variable {C : Type (max u v)} [Category.{v} C]
  (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasSheafify J (ModuleCat.{max u v} R)] (U : C)

def presheaf (P : Cᵒᵖ ⥤ ModuleCat.{max u v} R) :
    (Presheaf.freeYoneda U (ModuleCat.of R R) ⟶ P) ≃ₗ[R]
      (ModuleCat.of R R ⟶ P.obj (op U)) :=
  { AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaAddEquiv.FreeYonedaAddEquiv.presheaf U (ModuleCat.of R R) P with
    map_smul' := by
      intro r a
      change Sigma.ι (fun _ : U ⟶ U => ModuleCat.of R R) (𝟙 U) ≫
        (r • a.app (op U)) = _
      erw [Linear.comp_smul]
      rfl }

def homEquiv (M : Sheaf J (ModuleCat.{max u v} R)) :
    (Sheaf.freeYoneda J U (ModuleCat.of R R) ⟶ M) ≃ₗ[R] M.obj.obj (op U) :=
  (LinearAdjunction.homLinearEquiv R (sheafificationAdjunction J (ModuleCat.{max u v} R))
    (Presheaf.freeYoneda U (ModuleCat.of R R)) M).trans
      ((presheaf R U M.obj).trans
        (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R _)))

theorem homEquiv_natural {M N : Sheaf J (ModuleCat.{max u v} R)}
    (a : Sheaf.freeYoneda J U (ModuleCat.of R R) ⟶ M) (b : M ⟶ N) :
    homEquiv R J U N (a ≫ b) = b.hom.app (op U) (homEquiv R J U M a) :=
  PresentationSheafSections.freeSections_natural R J U b a

variable [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]

def equivalence (M : Sheaf J (ModuleCat.{max u v} R)) :
    Abelian.Ext.{max u v z} (Sheaf.freeYoneda J U (ModuleCat.of R R)) M 0 ≃ₗ[R]
      ULift.{z} (M.obj.obj (op U)) :=
  Abelian.Ext.linearEquiv₀.trans ((homEquiv R J U M).trans ULift.moduleEquiv.symm)

theorem equivalence_mk (M : Sheaf J (ModuleCat.{max u v} R))
    (a : Sheaf.freeYoneda J U (ModuleCat.of R R) ⟶ M) :
    equivalence R J U M (Abelian.Ext.mk₀ a) = ULift.up (homEquiv R J U M a) :=
  congrArg (fun b => ULift.up (homEquiv R J U M b)) (Abelian.Ext.linearEquiv₀.apply_symm_apply a)

def iso : IntegralComparison.Ext.ModuleFunctor.functor R (Sheaf.freeYoneda J U (ModuleCat.of R R)) 0 ≅
    sheafToPresheaf J (ModuleCat.{max u v} R) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{max u v} R)).obj (op U) ⋙
        ModuleCat.uliftFunctor.{z,max u v} R :=
  NatIso.ofComponents (fun M => (equivalence R J U M).toModuleIso) (by
    intro M N b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := (Abelian.Ext.mk₀_bijective (Sheaf.freeYoneda J U (ModuleCat.of R R)) M).2 x
    have h := (congrArg (equivalence R J U N) (Abelian.Ext.mk₀_comp_mk₀ a b)).trans
      ((equivalence_mk R J U N (a ≫ b)).trans
        (congrArg ULift.up (homEquiv_natural R J U a b)))
    exact h.trans (congrArg
      (fun y : ULift.{z} (M.obj.obj (op U)) => ULift.up (b.hom.app (op U) y.down))
      (equivalence_mk R J U M a).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaExtZeroEvaluation
