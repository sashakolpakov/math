import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ModulePullbackCoherence
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackSectionSquares

/-! # Pullback Square Composition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackSquareComposition.Construction

noncomputable section

/-! Composition of the actual module comparisons attached to two
successive commuting scheme squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem sectionPullbackSquareIso_eq_modulePullbackTo
    {X Y X' Y' : Scheme.{u}} (q : X ⟶ Y) (q' : X' ⟶ Y')
    (j : X' ⟶ X) (i : Y' ⟶ Y) (h : j ≫ q = q' ≫ i) (M : Y.Modules) :
    PullbackSectionSquares.Construction.sectionPullbackSquareIso q q' j i h M =
      ModulePullbackCoherence.Construction.modulePullbackTo j q (q' ≫ i) h M ≪≫ ((Scheme.Modules.pullbackComp q' i).app M).symm := by
  apply Iso.ext
  rfl

private theorem iso_cancel_rectangle {C : Type*} [Category* C] {W X Y Z : C}
    (a : W ≅ X) (b : X ≅ Z) (c : W ≅ Y) (d : Y ≅ Z)
    (h : a ≪≫ b = c ≪≫ d) : a.symm ≪≫ c = b ≪≫ d.symm := by
  apply Iso.ext
  apply (cancel_epi a.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  have hh : a.hom ≫ b.hom = c.hom ≫ d.hom := congrArg Iso.hom h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    (congrArg (fun f => f ≫ d.inv) hh).symm

set_option backward.isDefEq.respectTransparency false in
theorem sectionPullbackSquareIso_comp
    {X Y X₁ Y₁ X₂ Y₂ : Scheme.{u}}
    (q : X ⟶ Y) (q₁ : X₁ ⟶ Y₁) (q₂ : X₂ ⟶ Y₂)
    (j₁ : X₁ ⟶ X) (i₁ : Y₁ ⟶ Y) (j₂ : X₂ ⟶ X₁) (i₂ : Y₂ ⟶ Y₁)
    (h₁ : j₁ ≫ q = q₁ ≫ i₁) (h₂ : j₂ ≫ q₁ = q₂ ≫ i₂)
    (hc : (j₂ ≫ j₁) ≫ q = q₂ ≫ (i₂ ≫ i₁)) (M : Y.Modules) :
    (Scheme.Modules.pullback j₂).mapIso (PullbackSectionSquares.Construction.sectionPullbackSquareIso q q₁ j₁ i₁ h₁ M) ≪≫
        PullbackSectionSquares.Construction.sectionPullbackSquareIso q₁ q₂ j₂ i₂ h₂ ((Scheme.Modules.pullback i₁).obj M) ≪≫
        (Scheme.Modules.pullback q₂).mapIso ((Scheme.Modules.pullbackComp i₂ i₁).app M) =
      (Scheme.Modules.pullbackComp j₂ j₁).app ((Scheme.Modules.pullback q).obj M) ≪≫
        PullbackSectionSquares.Construction.sectionPullbackSquareIso q q₂ (j₂ ≫ j₁) (i₂ ≫ i₁) hc M := by
  let p := q₂ ≫ (i₂ ≫ i₁)
  have hp : j₂ ≫ (q₁ ≫ i₁) = p := by rw [← Category.assoc, h₂, Category.assoc]
  let A := ModulePullbackCoherence.Construction.modulePullbackTo j₁ q (q₁ ≫ i₁) h₁ M
  let B := (Scheme.Modules.pullbackComp q₁ i₁).app M
  let C := ModulePullbackCoherence.Construction.modulePullbackTo j₂ q₁ (q₂ ≫ i₂) h₂ ((Scheme.Modules.pullback i₁).obj M)
  let D := (Scheme.Modules.pullbackComp q₂ i₂).app ((Scheme.Modules.pullback i₁).obj M)
  let E := ModulePullbackCoherence.Construction.modulePullbackTo j₂ (q₁ ≫ i₁) p hp M
  let F := ModulePullbackCoherence.Construction.modulePullbackTo (q₂ ≫ i₂) i₁ p (Category.assoc q₂ i₂ i₁) M
  let G := (Scheme.Modules.pullbackComp q₂ (i₂ ≫ i₁)).app M
  let J := (Scheme.Modules.pullbackComp j₂ j₁).app ((Scheme.Modules.pullback q).obj M)
  let K := ModulePullbackCoherence.Construction.modulePullbackTo (j₂ ≫ j₁) q p hc M
  let P := (Scheme.Modules.pullback q₂).mapIso ((Scheme.Modules.pullbackComp i₂ i₁).app M)
  have hA : (Scheme.Modules.pullback j₂).mapIso A ≪≫ E = J ≪≫ K :=
    ModulePullbackCoherence.Construction.modulePullbackTo_natural q M j₂ j₁ (q₁ ≫ i₁) h₁ (j₂ ≫ j₁) p hc rfl hp
  have hB : (Scheme.Modules.pullback j₂).mapIso B ≪≫ E = C ≪≫ F :=
    ModulePullbackCoherence.Construction.modulePullbackTo_natural i₁ M j₂ q₁ (q₁ ≫ i₁) rfl (q₂ ≫ i₂) p
      (Category.assoc q₂ i₂ i₁) h₂ hp
  have hD : P ≪≫ G = D ≪≫ F :=
    ModulePullbackCoherence.Construction.modulePullbackTo_natural i₁ M q₂ i₂ (i₂ ≫ i₁) rfl (q₂ ≫ i₂) p
      (Category.assoc q₂ i₂ i₁) rfl rfl
  have hB' : ((Scheme.Modules.pullback j₂).mapIso B).symm ≪≫ C = E ≪≫ F.symm :=
    iso_cancel_rectangle _ _ _ _ hB
  have hD' : D.symm ≪≫ P = F ≪≫ G.symm := iso_cancel_rectangle _ _ _ _ hD.symm
  rw [sectionPullbackSquareIso_eq_modulePullbackTo q q₁ j₁ i₁ h₁ M,
    sectionPullbackSquareIso_eq_modulePullbackTo q₁ q₂ j₂ i₂ h₂ ((Scheme.Modules.pullback i₁).obj M),
    sectionPullbackSquareIso_eq_modulePullbackTo q q₂ (j₂ ≫ j₁) (i₂ ≫ i₁) hc M]
  rw [Functor.mapIso_trans, Functor.mapIso_symm]
  simp only [Iso.trans_assoc]
  rw [hD']
  rw [← Iso.trans_assoc ((Scheme.Modules.pullback j₂).mapIso B).symm C (F ≪≫ G.symm), hB']
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  exact ((Iso.trans_assoc _ _ _).symm.trans (congrArg (fun a => a ≪≫ G.symm) hA)).trans
    (Iso.trans_assoc _ _ _)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackSquareComposition.Construction
