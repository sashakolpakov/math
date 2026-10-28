import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSquareComponents
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OverSquare

/-! # Recovery Components -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.RecoveryComponents

noncomputable section

/-!
# Component formulas for the recovered native square isomorphisms
-/

open _root_.CategoryTheory Opposite _root_.AlgebraicGeometry

universe u v u' v'

section General

variable {C : Type u} [Category.{v} C] {S : C} {A B : Over S} (f : A ⟶ B)
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  (D : (DescentReindexing.reindex (Over.forget S) F).DescentData (fun (_ : PUnit.{1}) => f))
  (P : F.obj (.mk (op B.left)))

/-- Passing a genuine recovery to the underlying category retains its exact original source component. -/
theorem lowerIso_hom
    (e : Pseudofunctor.DescentData.ofObj (F := DescentReindexing.reindex (Over.forget S) F)
      (f := fun (_ : PUnit.{1}) => f) P ≅ D) :
    (Recovered.OverDescent.lowerIso f F D P e).hom.hom PUnit.unit = e.hom.hom PUnit.unit := by
  change (𝟙 _) ≫ e.hom.hom PUnit.unit = e.hom.hom PUnit.unit
  exact Category.id_comp _

end General

open _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {S : Scheme.{u}} {X Y X' Y' : Over S} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (hf : iX ≫ f = f' ≫ iY)
  (D : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f))
  (P : Y.left.Modules) (e : (Scheme.Modules.pullback f.left).obj P ≅ D.obj PUnit.unit)
  (he : (Scheme.Modules.pullback (pullback.fst f.left f.left)).map e.hom ≫
      (Geometric.CechInvariant.relationGluing f.left (UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks
        (fun (_ : PUnit.{1}) => f) D)).hom =
    (Cech.MateNormalization.standardGluing f.left (pullback.fst f.left f.left) (pullback.snd f.left f.left)
      pullback.condition).hom.app P ≫ (Scheme.Modules.pullback (pullback.snd f.left f.left)).map e.hom)

/-- The original recovery isomorphism has precisely the given geometric source map. -/
theorem originalIso_hom : (Recovered.OverSquare.originalIso f D P e he).hom.hom PUnit.unit = e.hom := rfl

/-- The square recovery consists of the native square comparison followed by the pulled original recovery. -/
theorem recovery_hom : (Recovered.OverSquare.recovery f f' iX iY hf D P e he).hom =
    (DescentComponentIsomorphisms.componentIso (Geometric.KernelLinearization.overModulePullbacks S) f'
      (DescentSquareIsomorphisms.canonicalIso (Geometric.KernelLinearization.overModulePullbacks S) f f' iX iY hf P)).inv ≫
        (Scheme.Modules.pullback iX.left).map e.hom := by
  change (Recovered.OverDescent.lowerIso f' Geometric.KernelLinearization.modulePullbacks
    (Recovered.OverSquare.pulledDatum f f' iX iY hf D) ((Scheme.Modules.pullback iY.left).obj P)
    (Recovered.OverSquare.pulledIso f f' iX iY hf D P e he)).hom.hom PUnit.unit = _
  exact lowerIso_hom f' Geometric.KernelLinearization.modulePullbacks (Recovered.OverSquare.pulledDatum f f' iX iY hf D)
    ((Scheme.Modules.pullback iY.left).obj P) (Recovered.OverSquare.pulledIso f f' iX iY hf D P e he)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.RecoveryComponents
