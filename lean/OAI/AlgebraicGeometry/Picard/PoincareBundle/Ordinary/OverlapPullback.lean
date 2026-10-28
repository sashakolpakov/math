import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.OverlapGluing

/-! # Overlap Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OverlapPullback

noncomputable section

/-!
# Ordinary geometric descent identifies the gluing on every changed overlap
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

variable {X Y Z W : Scheme.{u}} (f : X ⟶ Y)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
  (base : Z ⟶ Y) (p q : Z ⟶ X) (hp : p ≫ f = base) (hq : q ≫ f = base)

/-- The ordinary descent isomorphism on a specified overlap. -/
def overlapIso : (Scheme.Modules.pullback p).obj (D.obj PUnit.unit) ≅
    (Scheme.Modules.pullback q).obj (D.obj PUnit.unit) :=
  D.iso base (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hp hq

theorem overlapIso_hom : (overlapIso f D base p q hp hq).hom =
    D.hom base (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hp hq :=
  Pseudofunctor.DescentData.iso_hom D base p q hp hq

variable (r : W ⟶ Z)

/-- The same ordinary descent isomorphism evaluated on the pulled-back overlap coordinates. -/
def pulledOverlapIso :
    (Scheme.Modules.pullback (r ≫ p)).obj (D.obj PUnit.unit) ≅
      (Scheme.Modules.pullback (r ≫ q)).obj (D.obj PUnit.unit) :=
  overlapIso f D (r ≫ base) (r ≫ p) (r ≫ q)
    ((Category.assoc r p f).trans (congrArg (fun z => r ≫ z) hp))
    ((Category.assoc r q f).trans (congrArg (fun z => r ≫ z) hq))

/-- Pulling back the gluing recovers exactly the gluing provided by ordinary descent. -/
theorem overlapIso_pullback :
    Geometric.OverlapGluing.extendedGluing p q r (D.obj PUnit.unit) (overlapIso f D base p q hp hq) =
      pulledOverlapIso f D base p q hp hq r := by
  apply Iso.ext
  have he := Intrinsic.OverlapGluing.hasNativeFormula p q r (D.obj PUnit.unit)
    (overlapIso f D base p q hp hq)
  have hs := overlapIso_hom f D base p q hp hq
  have ht := overlapIso_hom f D (r ≫ base) (r ≫ p) (r ≫ q)
    ((Category.assoc r p f).trans (congrArg (fun z => r ≫ z) hp))
    ((Category.assoc r q f).trans (congrArg (fun z => r ≫ z) hq))
  have hd := Geometric.DescentEquations.hom_pullback D r base (r ≫ base) rfl (i := PUnit.unit) (j := PUnit.unit)
    p q hp hq (r ≫ p) (r ≫ q) rfl rfl
  exact he.trans ((congrArg (fun a => Geometric.DescentEquations.nativePullback a r (r ≫ p) (r ≫ q) rfl rfl) hs).trans
    (hd.trans ht.symm))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OverlapPullback
