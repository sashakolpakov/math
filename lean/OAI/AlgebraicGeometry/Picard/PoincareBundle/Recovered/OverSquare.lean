import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OverDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.SquareDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSquareIsomorphisms

/-! # Over Square -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OverSquare

noncomputable section

/-!
# Native square pullback gives compatible geometric recoveries over a fixed base
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary

variable {S : Scheme.{u}} {X Y X' Y' : Over S} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (hf : iX ≫ f = f' ≫ iY)
  (D : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f))

/-- The genuine pullback functor for a commuting square over the original base. -/
def squareFunctor : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f) ⥤
    (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f') :=
  Pseudofunctor.DescentData.pullFunctor (Geometric.KernelLinearization.overModulePullbacks S)
    (f := fun (_ : PUnit.{1}) => f) (f' := fun (_ : PUnit.{1}) => f') (p := iY)
    (α := fun (_ : PUnit.{1}) => PUnit.unit) (p' := fun (_ : PUnit.{1}) => iX) (fun _ => hf)

/-- Pull back the actual descent datum before forgetting the base. -/
def pulledDatum : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f') :=
  (squareFunctor f f' iX iY hf).obj D

/-- Its underlying geometric datum retains the common original test-object structure. -/
def underlyingDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f'.left) :=
  UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => f')
    (pulledDatum f f' iX iY hf D)

/-- The native square gluing uses the actual geometric composition isomorphisms. -/
theorem pulledHom {T : Over S} (q : T ⟶ Y') (x y : T ⟶ X')
    (hx : x ≫ f' = q) (hy : y ≫ f' = q) :
    (pulledDatum f f' iX iY hf D).hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      (Scheme.Modules.pullbackComp x.left iX.left).hom.app (D.obj PUnit.unit) ≫
        D.hom (q ≫ iY) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (x ≫ iX) (y ≫ iX)
          (by rw [Category.assoc, hf, ← Category.assoc, hx])
          (by rw [Category.assoc, hf, ← Category.assoc, hy]) ≫
        (Scheme.Modules.pullbackComp y.left iX.left).inv.app (D.obj PUnit.unit) := by
  cases hx
  rfl

variable (P : Y.left.Modules) (e : (Scheme.Modules.pullback f.left).obj P ≅ D.obj PUnit.unit)
  (he : (Scheme.Modules.pullback (pullback.fst f.left f.left)).map e.hom ≫
      (Geometric.CechInvariant.relationGluing f.left (UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks
        (fun (_ : PUnit.{1}) => f) D)).hom =
    (Cech.MateNormalization.standardGluing f.left (pullback.fst f.left f.left) (pullback.snd f.left f.left)
      pullback.condition).hom.app P ≫ (Scheme.Modules.pullback (pullback.snd f.left f.left)).map e.hom)

/-- The original compatible geometric recovery is an actual isomorphism over the base. -/
def originalIso : Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.overModulePullbacks S)
    (f := fun (_ : PUnit.{1}) => f) P ≅ D :=
  OverDescent.liftIso f Geometric.KernelLinearization.modulePullbacks D P
    (SquareDescent.originalIso f.left
      (UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => f) D) P e he)

/-- Canonical recovery commutes with the genuine square pullback functor. -/
def canonicalSquareIso :
    (squareFunctor f f' iX iY hf).obj
      (Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.overModulePullbacks S) (f := fun (_ : PUnit.{1}) => f) P) ≅
    Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.overModulePullbacks S) (f := fun (_ : PUnit.{1}) => f')
      ((Scheme.Modules.pullback iY.left).obj P) :=
  DescentSquareIsomorphisms.canonicalIso (Geometric.KernelLinearization.overModulePullbacks S) f f' iX iY hf P

/-- The recovered isomorphism on the square is constructed by functoriality. -/
def pulledIso :
    Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.overModulePullbacks S) (f := fun (_ : PUnit.{1}) => f')
      ((Scheme.Modules.pullback iY.left).obj P) ≅ pulledDatum f f' iX iY hf D :=
  (canonicalSquareIso f f' iX iY hf P).symm ≪≫
    (squareFunctor f f' iX iY hf).mapIso (originalIso f D P e he)

/-- The square recovery is also an actual isomorphism of the complete underlying geometric data. -/
def underlyingRecoveryIso : OrdinaryDatum.Ordinary.baseDatum f'.left ((Scheme.Modules.pullback iY.left).obj P) ≅
    underlyingDatum f f' iX iY hf D :=
  OverDescent.lowerIso f' Geometric.KernelLinearization.modulePullbacks (pulledDatum f f' iX iY hf D)
    ((Scheme.Modules.pullback iY.left).obj P) (pulledIso f f' iX iY hf D P e he)

/-- The actual source recovery obtained from this descent isomorphism. -/
def recovery : (Scheme.Modules.pullback f'.left).obj ((Scheme.Modules.pullback iY.left).obj P) ≅
    (Scheme.Modules.pullback iX.left).obj (D.obj PUnit.unit) :=
  DescentComponentIsomorphisms.componentIso Geometric.KernelLinearization.modulePullbacks f'.left
    (underlyingRecoveryIso f f' iX iY hf D P e he)

/-- Its full geometric kernel-pair compatibility follows from the constructed descent isomorphism. -/
theorem recovery_compatible :
    (Scheme.Modules.pullback (pullback.fst f'.left f'.left)).map (recovery f f' iX iY hf D P e he).hom ≫
      (Geometric.CechInvariant.relationGluing f'.left (underlyingDatum f f' iX iY hf D)).hom =
    (Cech.MateNormalization.standardGluing f'.left (pullback.fst f'.left f'.left) (pullback.snd f'.left f'.left)
      pullback.condition).hom.app ((Scheme.Modules.pullback iY.left).obj P) ≫
        (Scheme.Modules.pullback (pullback.snd f'.left f'.left)).map (recovery f f' iX iY hf D P e he).hom := by
  have h := (underlyingRecoveryIso f f' iX iY hf D P e he).hom.comm
    (pullback.snd f'.left f'.left ≫ f'.left) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
    (pullback.fst f'.left f'.left) (pullback.snd f'.left f'.left) pullback.condition rfl
  change (Scheme.Modules.pullback (pullback.fst f'.left f'.left)).map (recovery f f' iX iY hf D P e he).hom ≫
      (Geometric.CechInvariant.relationGluing f'.left (underlyingDatum f f' iX iY hf D)).hom =
    (Geometric.CechInvariant.relationGluing f'.left (OrdinaryDatum.Ordinary.baseDatum f'.left ((Scheme.Modules.pullback iY.left).obj P))).hom ≫
      (Scheme.Modules.pullback (pullback.snd f'.left f'.left)).map (recovery f f' iX iY hf D P e he).hom at h
  rw [OrdinaryDatum.Ordinary.baseDatum_gluing] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OverSquare
