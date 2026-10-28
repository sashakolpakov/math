import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits

/-! # Iso Ratios -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios

noncomputable section

/-! Ratios of actual line isomorphisms, including composition and arbitrary pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits

variable {X Y : Scheme.{u}} {M N P : X.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M)

/-- The unique scalar relating two actual isomorphisms with the same endpoints. -/
def ratio (e f : M ≅ N) : Γ(X, ⊤)ˣ := AutomorphismUnits.unitOfAut hM (e ≪≫ f.symm)

theorem ratio_spec (e f : M ≅ N) :
    Isogenies.NeighborCounting.ModuleScalar.scalarEnd M (ratio hM e f).val ≫ f.hom = e.hom := by
  have h := congrArg Iso.hom (AutomorphismUnits.scalarIso_unitOfAut hM (e ≪≫ f.symm))
  change Isogenies.NeighborCounting.ModuleScalar.scalarEnd M (ratio hM e f).val = e.hom ≫ f.inv at h
  rw [h, Category.assoc, f.inv_hom_id, Category.comp_id]

theorem ratio_eq_one_iff (e f : M ≅ N) : ratio hM e f = 1 ↔ e = f := by
  constructor
  · intro h
    apply Iso.ext
    have hs := ratio_spec hM e f
    rw [h] at hs
    simpa only [Units.val_one, Isogenies.NeighborCounting.ModuleScalar.scalarEnd_one, Category.id_comp] using hs.symm
  · intro h
    subst f
    change AutomorphismUnits.unitOfAut hM (e ≪≫ e.symm) = 1
    simpa only [Iso.self_symm_id] using AutomorphismUnits.unitOfAut_refl hM

theorem ratio_postcomp (e f : M ≅ N) (g : N ≅ P) :
    ratio hM (e ≪≫ g) (f ≪≫ g) = ratio hM e f := by
  apply congrArg (AutomorphismUnits.unitOfAut hM)
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc]

theorem ratio_precomp {Q : X.Modules} (hQ : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle Q) (s : Q ≅ M) (e f : M ≅ N) :
    ratio hQ (s ≪≫ e) (s ≪≫ f) = ratio hM e f := by
  have h := AutomorphismUnits.unitOfAut_conjugate hM hQ s.symm (e ≪≫ f.symm)
  exact h

theorem ratio_chain (e f g : M ≅ N) :
    ratio hM e f * ratio hM f g = ratio hM e g := by
  rw [ratio, ratio, ← AutomorphismUnits.unitOfAut_trans]
  apply congrArg (AutomorphismUnits.unitOfAut hM)
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

theorem ratio_comp (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N) (e f : M ≅ N) (g h : N ≅ P) :
    ratio hM (e ≪≫ g) (f ≪≫ h) = ratio hM e f * ratio hN g h := by
  have hc := ratio_chain hM (e ≪≫ g) (f ≪≫ g) (f ≪≫ h)
  rw [ratio_postcomp, ratio_precomp hN hM f] at hc
  exact hc.symm

/-- Ratios remain regular units on every scheme after arbitrary base change. -/
theorem ratio_pullback (a : Y ⟶ X) (e f : M ≅ N) :
    ratio (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback a M hM)
      ((Scheme.Modules.pullback a).mapIso e) ((Scheme.Modules.pullback a).mapIso f) =
      Units.map a.appTop.hom (ratio hM e f) := by
  simpa only [ratio, Functor.mapIso_trans, Functor.mapIso_symm] using
    AutomorphismUnits.unitOfAut_pullback hM a (e ≪≫ f.symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios
