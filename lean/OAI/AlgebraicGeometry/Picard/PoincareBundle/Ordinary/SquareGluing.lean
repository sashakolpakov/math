import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OverlapPullback

/-! # Square Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

noncomputable section

/-!
# Ordinary geometric descent and a commuting square of covers
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OverlapPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (hf : iX ≫ f = f' ≫ iY)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))

/-- Restrict ordinary descent data through the actual commuting square of covers. -/
def pulledDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f') :=
  (Pseudofunctor.DescentData.pullFunctor Geometric.KernelLinearization.modulePullbacks
    (f := fun (_ : PUnit.{1}) => f) (f' := fun (_ : PUnit.{1}) => f') (p := iY)
    (α := fun (_ : PUnit.{1}) => PUnit.unit) (p' := fun (_ : PUnit.{1}) => iX) (fun _ => hf)).obj D

/-- Its actual gluing uses the standard geometric pullback composition maps. -/
theorem pulledHom {Z' : Scheme.{u}} (base' : Z' ⟶ Y') (p' q' : Z' ⟶ X')
    (hp' : p' ≫ f' = base') (hq' : q' ≫ f' = base') :
    (pulledDatum f f' iX iY hf D).hom base' (i₁ := PUnit.unit) (i₂ := PUnit.unit) p' q' hp' hq' =
      (Scheme.Modules.pullbackComp p' iX).hom.app (D.obj PUnit.unit) ≫
        D.hom (base' ≫ iY) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p' ≫ iX) (q' ≫ iX)
          (by rw [Category.assoc, hf, ← Category.assoc, hp'])
          (by rw [Category.assoc, hf, ← Category.assoc, hq']) ≫
        (Scheme.Modules.pullbackComp q' iX).inv.app (D.obj PUnit.unit) := by
  cases hp'
  rfl

end

section

variable {X Z X' Z' : Scheme.{u}} (p : Z ⟶ X) (p' : Z' ⟶ X')
  (iX : X' ⟶ X) (iZ : Z' ⟶ Z) (hp : iZ ≫ p = p' ≫ iX)

/-- The geometric pullback square in the orientation used by ordinary descent restriction. -/
def pullbackSquare : Scheme.Modules.pullback iX ⋙ Scheme.Modules.pullback p' ≅
    Scheme.Modules.pullback p ⋙ Scheme.Modules.pullback iZ :=
  Scheme.Modules.pullbackComp p' iX ≪≫
    (Scheme.Modules.pullbackComp iZ p ≪≫ Scheme.Modules.pullbackCongr hp).symm

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OverlapPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

variable {X Y Z X' Y' Z' : Scheme.{u}}
  (f : X ⟶ Y) (f' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y) (hf : iX ≫ f = f' ≫ iY)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
  (base : Z ⟶ Y) (p q : Z ⟶ X) (hp : p ≫ f = base) (hq : q ≫ f = base)
  (base' : Z' ⟶ Y') (p' q' : Z' ⟶ X') (hp' : p' ≫ f' = base') (hq' : q' ≫ f' = base')
  (iZ : Z' ⟶ Z) (hb : iZ ≫ base = base' ≫ iY)
  (heP : iZ ≫ p = p' ≫ iX) (heQ : iZ ≫ q = q' ≫ iX)

/-- The actual gluing transported through the geometric squares. -/
def squareGluing :
    (Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback iX).obj (D.obj PUnit.unit)) ≅
      (Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback iX).obj (D.obj PUnit.unit)) :=
  (pullbackSquare p p' iX iZ heP).app (D.obj PUnit.unit) ≪≫
    (Scheme.Modules.pullback iZ).mapIso (OverlapPullback.overlapIso f D base p q hp hq) ≪≫
      ((pullbackSquare q q' iX iZ heQ).app (D.obj PUnit.unit)).symm

include hb in
/-- The square-transported gluing is exactly the original ordinary restricted descent gluing. -/
theorem squareGluing_eq : squareGluing f iX D base p q hp hq p' q' iZ heP heQ =
    OverlapPullback.overlapIso f' (pulledDatum f f' iX iY hf D) base' p' q' hp' hq' := by
  apply Iso.ext
  rw [OverlapPullback.overlapIso_hom, pulledHom]
  have hn := Geometric.DescentEquations.hom_pullback D iZ base (base' ≫ iY) hb (i := PUnit.unit) (j := PUnit.unit)
    p q hp hq (p' ≫ iX) (q' ≫ iX) heP heQ
  rw [← hn]
  simp only [squareGluing, pullbackSquare, Functor.mapIso_hom,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Geometric.DescentEquations.nativePullback]
  rw [OverlapPullback.overlapIso_hom]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing
