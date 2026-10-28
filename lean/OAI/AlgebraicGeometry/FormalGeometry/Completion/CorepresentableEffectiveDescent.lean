import OAI.AlgebraicGeometry.FormalGeometry.Completion.DescentSectionsTo

/-! # Corepresentable Effective Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CorepresentableEffectiveDescent.Construction

noncomputable section

/-!
# Completion: effective descent of a corepresentative

When sections satisfy the descent equalizer and the algebra comparison is
fully faithful, an object recovering the local canonical coalgebra actually
corepresents the original functor. This supplies the identification step.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v' w

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (F : C ⥤ Type w)
  {Y : D} (rep : (R ⋙ F).CorepresentableBy Y)
  (hcomparison : (Comonad.comparison adj).FullyFaithful)
  (hsections : ∀ T, Function.Bijective (DescentSectionsTo.Construction.sectionToDescent adj F T))
  {A : C} (e : (Comonad.comparison adj).obj A ≅ CorepresentableDescent.Construction.corepresentableDescentCoalgebra adj F rep)

/-- Morphisms from the descended object are in bijection with original sections. -/
def descendedCorepresentativeHomEquiv (T : C) : (A ⟶ T) ≃ F.obj T :=
  hcomparison.homEquiv.trans
    ((Iso.homCongr e (Iso.refl _)).trans
      ((DescentSectionsTo.Construction.corepresentableCoalgebraHomEquiv adj F rep T).trans
        (Equiv.ofBijective (DescentSectionsTo.Construction.sectionToDescent adj F T) (hsections T)).symm))

theorem descendedCorepresentativeHomEquiv_restrict {T : C} (g : A ⟶ T) :
    F.map (adj.unit.app T)
        (descendedCorepresentativeHomEquiv adj F rep hcomparison hsections e T g) =
      rep.homEquiv (e.inv.f ≫ L.map g) := by
  simpa only [descendedCorepresentativeHomEquiv, Equiv.trans_apply,
    Functor.FullyFaithful.homEquiv_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
    DescentSectionsTo.Construction.sectionToDescent, DescentSectionsTo.Construction.corepresentableCoalgebraHomEquiv]
    using! congrArg Subtype.val
    (Equiv.ofBijective_apply_symm_apply (DescentSectionsTo.Construction.sectionToDescent adj F T) (hsections T)
      ((DescentSectionsTo.Construction.corepresentableCoalgebraHomEquiv adj F rep T)
        (e.inv ≫ (Comonad.comparison adj).map g)))

/-- The section bijections commute with all morphisms, so the descended object corepresents the functor. -/
def descendedCorepresentative : F.CorepresentableBy A where
  homEquiv := descendedCorepresentativeHomEquiv adj F rep hcomparison hsections e _
  homEquiv_comp {T T'} g h := by
    apply (hsections T').injective
    apply Subtype.ext
    change F.map (adj.unit.app T')
      (descendedCorepresentativeHomEquiv adj F rep hcomparison hsections e T' (h ≫ g)) =
        F.map (adj.unit.app T')
          (F.map g (descendedCorepresentativeHomEquiv adj F rep hcomparison hsections e T h))
    rw [descendedCorepresentativeHomEquiv_restrict]
    calc
      rep.homEquiv (e.inv.f ≫ L.map (h ≫ g)) =
          F.map (R.map (L.map g)) (rep.homEquiv (e.inv.f ≫ L.map h)) := by
        rw [CategoryTheory.Functor.map_comp, ← Category.assoc]
        exact rep.homEquiv_comp _ _
      _ = _ := by
        rw [← descendedCorepresentativeHomEquiv_restrict adj F rep hcomparison hsections e h]
        erw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        exact congrArg (fun k => F.map k
          (descendedCorepresentativeHomEquiv adj F rep hcomparison hsections e T h))
            (adj.unit.naturality g).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CorepresentableEffectiveDescent.Construction
