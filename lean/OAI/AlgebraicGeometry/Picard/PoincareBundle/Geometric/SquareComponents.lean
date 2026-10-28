import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.RecoveryComponents
import OAI.AlgebraicGeometry.Picard.PoincareBundle.OverFiberComposition

/-! # Square Components -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.SquareComponents

noncomputable section

/-!
# Explicit geometric formulas for the compatible native square recovery
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {S : Scheme.{u}} {X Y X' Y' : Over S} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (hf : iX ≫ f = f' ≫ iY) (P : Y.left.Modules)

/-- The native canonical square component has exactly the usual geometric composition formula. -/
theorem canonical_component :
    DescentComponentIsomorphisms.componentIso (KernelLinearization.overModulePullbacks S) f'
      (DescentSquareIsomorphisms.canonicalIso (KernelLinearization.overModulePullbacks S) f f' iX iY hf P) =
    (Scheme.Modules.pullbackComp iX.left f.left ≪≫
      Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hf)).app P ≪≫
      ((Scheme.Modules.pullbackComp f'.left iY.left).app P).symm := by
  have h := DescentSquareComponents.canonical_component (KernelLinearization.overModulePullbacks S) f f' iX iY hf P
  have hi := OverFiberComposition.fiberIsoTo_eq f P iX (f' ≫ iY) hf
  have hj := congrArg Iso.symm (OverFiberComposition.fiberIso_eq iY P f')
  have hcomp := congrArg₂ Iso.trans hi hj
  exact h.trans hcomp

variable (D : (KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f))
  (e : (Scheme.Modules.pullback f.left).obj P ≅ D.obj PUnit.unit)
  (he : (Scheme.Modules.pullback (pullback.fst f.left f.left)).map e.hom ≫
      (CechInvariant.relationGluing f.left (UnderlyingDescent.underlyingDatum KernelLinearization.modulePullbacks
        (fun (_ : PUnit.{1}) => f) D)).hom =
    (Cech.MateNormalization.standardGluing f.left (pullback.fst f.left f.left) (pullback.snd f.left f.left)
      pullback.condition).hom.app P ≫ (Scheme.Modules.pullback (pullback.snd f.left f.left)).map e.hom)

/-- The constructed compatible recovery is the explicit composition square followed by the original recovered line map. -/
theorem recovery_eq : Recovered.OverSquare.recovery f f' iX iY hf D P e he =
    (Scheme.Modules.pullbackComp f'.left iY.left).app P ≪≫
      ((Scheme.Modules.pullbackComp iX.left f.left ≪≫
        Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hf)).app P).symm ≪≫
      (Scheme.Modules.pullback iX.left).mapIso e := by
  apply Iso.ext
  have h := Intrinsic.RecoveryComponents.recovery_hom f f' iX iY hf D P e he
  exact h.trans (congrArg (fun a => a ≫ (Scheme.Modules.pullback iX.left).map e.hom)
    (congrArg Iso.inv (canonical_component f f' iX iY hf P)))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.SquareComponents
