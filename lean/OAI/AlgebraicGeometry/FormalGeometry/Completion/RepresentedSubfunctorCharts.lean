import OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctor
import OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismPullbackCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-! # Represented Subfunctor Charts -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctorCharts

noncomputable section

/-! Represented subfunctors recover their local charts by actual
Cartesian squares. Properties local on the target descend from them. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

namespace Construction

universe u v
section Category

variable {C : Type u} [Category.{v} C] {S T M : C} (P : Subfunctor (yoneda.obj S))
  [P.toFunctor.IsRepresentable] (a : T ⟶ S) (m : M ⟶ T)
  (h : ∀ (Z : C) (j : Z ⟶ T), (j ≫ a) ∈ P.obj (op Z) ↔ ∃ z : Z ⟶ M, z ≫ m = j)

def representedSubfunctorChartMap : M ⟶ (RepresentedSubfunctor.Construction.representedSubfunctorFamily P).left :=
  P.toFunctor.representableBy.homEquiv.symm ⟨m ≫ a, (h M m).mpr ⟨𝟙 M, Category.id_comp m⟩⟩

theorem representedSubfunctorChartMap_comp :
    representedSubfunctorChartMap P a m h ≫ (RepresentedSubfunctor.Construction.representedSubfunctorFamily P).hom = m ≫ a :=
  (RepresentedSubfunctor.Construction.representedSubfunctor_value P (representedSubfunctorChartMap P a m h)).symm.trans
    (congrArg Subtype.val (P.toFunctor.representableBy.homEquiv.apply_symm_apply
      ⟨m ≫ a, (h M m).mpr ⟨𝟙 M, Category.id_comp m⟩⟩))

theorem representedSubfunctorChart_isPullback [Mono m] :
    IsPullback (representedSubfunctorChartMap P a m h) m (RepresentedSubfunctor.Construction.representedSubfunctorFamily P).hom a := by
  apply MonomorphismPullbackCriterion.Construction.monoSquare_isPullback _ _ _ _ (representedSubfunctorChartMap_comp P a m h)
  intro Z x j hxj
  have hx := (P.toFunctor.representableBy.homEquiv x).property
  rw [RepresentedSubfunctor.Construction.representedSubfunctor_value, hxj] at hx
  exact (h Z j).mp hx

end Category

theorem representedSubfunctor_localProperty {S : Scheme.{u}}
    (P : Subfunctor (yoneda.obj S)) [P.toFunctor.IsRepresentable]
    (U : S.OpenCover.{u}) (M : ∀ i, Over (U.X i)) [∀ i, Mono (M i).hom]
    (h : ∀ i (Z : Scheme.{u}) (j : Z ⟶ U.X i),
      (j ≫ U.f i) ∈ P.obj (op Z) ↔ ∃ z : Z ⟶ (M i).left, z ≫ (M i).hom = j)
    (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q]
    (hQ : ∀ i, Q (M i).hom) : Q (RepresentedSubfunctor.Construction.representedSubfunctorFamily P).hom := by
  apply IsZariskiLocalAtTarget.of_openCover U
  intro i
  let hp := representedSubfunctorChart_isPullback P (U.f i) (M i).hom (h i)
  let e : Arrow.mk (M i).hom ≅ Arrow.mk (U.pullbackHom (RepresentedSubfunctor.Construction.representedSubfunctorFamily P).hom i) :=
    Arrow.isoMk hp.isoPullback (Iso.refl _) (by
      change hp.isoPullback.hom ≫ pullback.snd (RepresentedSubfunctor.Construction.representedSubfunctorFamily P).hom (U.f i) =
        (M i).hom ≫ 𝟙 (U.X i)
      exact hp.isoPullback_hom_snd.trans (Category.comp_id (M i).hom).symm)
  exact (Q.arrow_mk_iso_iff e).mp (hQ i)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctorCharts
