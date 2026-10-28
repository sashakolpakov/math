import OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackEqualityComparisons
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr

/-! # Pullback Square Pasting -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackSquarePasting

noncomputable section

/-! Pasting two commuting squares gives the same actual module-pullback
comparison as composing their individual comparisons. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

@[reassoc]
theorem pullbackSquare_paste {X Y Z S T U : Scheme.{u}}
    (f : Y ⟶ X) (j : Z ⟶ Y) (s : S ⟶ X) (b : T ⟶ Y) (g : T ⟶ S)
    (c : U ⟶ Z) (t : U ⟶ T) (h : c ≫ j = t ≫ b) (h₀ : b ≫ f = g ≫ s)
    (h₁ : c ≫ (j ≫ f) = (t ≫ g) ≫ s) (M : X.Modules) :
    (Scheme.Modules.pullback c).map ((Scheme.Modules.pullbackComp j f).hom.app M) ≫
      (Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso (j ≫ f) s c (t ≫ g) h₁ M).hom =
    (Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso j b c t h ((Scheme.Modules.pullback f).obj M)).hom ≫
      (Scheme.Modules.pullback t).map (Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso f s b g h₀ M).hom ≫
        (Scheme.Modules.pullbackComp t g).hom.app ((Scheme.Modules.pullback s).obj M) := by
  apply (cancel_mono ((Scheme.Modules.pullbackComp (t ≫ g) s).hom.app M)).mp
  simp only [Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← PullbackTripleComparison.Construction.pullbackComp_three t g s M]
  have hi : (Scheme.Modules.pullback t).map ((Scheme.Modules.pullbackComp g s).inv.app M) ≫
      (Scheme.Modules.pullback t).map ((Scheme.Modules.pullbackComp g s).hom.app M) = 𝟙 _ :=
    ((Scheme.Modules.pullback t).mapIso ((Scheme.Modules.pullbackComp g s).app M)).inv_hom_id
  simp only [reassoc_of% hi]
  rw [PullbackEqualityComparisons.Construction.pullbackComp_congr_right_assoc t h₀ M, PullbackEqualityComparisons.Construction.pullbackComp_three_forward_assoc t b f M]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [PullbackEqualityComparisons.Construction.pullbackComp_congr_left_assoc h f M, PullbackEqualityComparisons.Construction.pullbackComp_three_forward_assoc c j f M]
  simp only [PullbackEqualityComparisons.Construction.pullbackCongr_trans]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackSquarePasting
