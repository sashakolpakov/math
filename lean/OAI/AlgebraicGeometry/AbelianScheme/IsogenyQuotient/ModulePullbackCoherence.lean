import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom

/-! # Module Pullback Coherence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ModulePullbackCoherence.Construction

noncomputable section

/-! Native module pullback comparisons with specified composites are
compatible with further pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

universe u

def modulePullbackTo {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) (M : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback k).obj M :=
  (Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h).app M

theorem modulePullbackTo_eq_fiberIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) (M : Z.Modules) :
    modulePullbackTo f g k h M =
      Picard.PoincareBundle.PullbackFiberComposition.fiberIsoTo Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks g M f k h := by
  subst k
  rfl

theorem modulePullbackTo_natural {X Y T T' : Scheme.{u}}
    (q : X ⟶ Y) (M : Y.Modules) (a : T' ⟶ T)
    (k : T ⟶ X) (p : T ⟶ Y) (hk : k ≫ q = p)
    (k' : T' ⟶ X) (p' : T' ⟶ Y) (hk' : k' ≫ q = p')
    (hak : a ≫ k = k') (hap : a ≫ p = p') :
    (Scheme.Modules.pullback a).mapIso (modulePullbackTo k q p hk M) ≪≫
        modulePullbackTo a p p' hap M =
      modulePullbackTo a k k' hak ((Scheme.Modules.pullback q).obj M) ≪≫
        modulePullbackTo k' q p' hk' M := by
  have hn := Picard.PoincareBundle.PullbackFiberComposition.fiberIsoTo_hom_pullback Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks
    q M a k p hk k' p' hk' hak hap
  rw [← modulePullbackTo_eq_fiberIso, ← modulePullbackTo_eq_fiberIso] at hn
  have he := Picard.PoincareBundle.Geometric.PullHom.pullHom_eq (modulePullbackTo k q p hk M).hom
    a k' p' hak hap
  have h := he.symm.trans hn
  apply Iso.ext
  apply (cancel_epi (modulePullbackTo a k k' hak ((Scheme.Modules.pullback q).obj M)).inv).mp
  change (modulePullbackTo a k k' hak ((Scheme.Modules.pullback q).obj M)).inv ≫
      (Scheme.Modules.pullback a).map (modulePullbackTo k q p hk M).hom ≫
        (modulePullbackTo a p p' hap M).hom =
    (modulePullbackTo a k k' hak ((Scheme.Modules.pullback q).obj M)).inv ≫
      (modulePullbackTo a k k' hak ((Scheme.Modules.pullback q).obj M)).hom ≫
        (modulePullbackTo k' q p' hk' M).hom
  exact h.trans ((modulePullbackTo a k k' hak ((Scheme.Modules.pullback q).obj M)).inv_hom_id_assoc _).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ModulePullbackCoherence.Construction
