import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentComponentIsomorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.RecoveredFibers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

/-! # Square Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.SquareDescent

noncomputable section

/-!
# A compatible actual recovery pulls back through an arbitrary square of covers

The recovery on the square is constructed by the native descent pullback functor. Its full
geometric compatibility is a theorem of the constructed descent isomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (hf : iX ≫ f = f' ≫ iY)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f)) (P : Y.Modules)
  (e : (Scheme.Modules.pullback f).obj P ≅ D.obj PUnit.unit)
  (he : (Scheme.Modules.pullback (pullback.fst f f)).map e.hom ≫ (Geometric.CechInvariant.relationGluing f D).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f) pullback.condition).hom.app P ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map e.hom)

/-- The original geometric recovery defines a morphism of the full ordinary descent data. -/
def originalHom : OrdinaryDatum.Ordinary.baseDatum f P ⟶ D :=
  Kernel.PairDetectsMorphisms.descentHom Geometric.KernelLinearization.modulePullbacks f (OrdinaryDatum.Ordinary.baseDatum f P) D e.hom
    (Geometric.RecoveredFibers.kernelPair_compatible f D P e he)

/-- The actual recovered source isomorphism is an isomorphism of the complete original descent data. -/
def originalIso : OrdinaryDatum.Ordinary.baseDatum f P ≅ D := by
  have : IsIso ((originalHom f D P e he).hom PUnit.unit) := e.isIso_hom
  exact DescentComponentIsomorphisms.isoOfComponent Geometric.KernelLinearization.modulePullbacks f (originalHom f D P e he)

/-- The native descent pullback functor for the given actual commuting square. -/
def squareFunctor : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f) ⥤
    Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f') :=
  Pseudofunctor.DescentData.pullFunctor Geometric.KernelLinearization.modulePullbacks
    (f := fun (_ : PUnit.{1}) => f) (f' := fun (_ : PUnit.{1}) => f') (p := iY)
    (α := fun (_ : PUnit.{1}) => PUnit.unit) (p' := fun (_ : PUnit.{1}) => iX) (fun _ => hf)

/-- Pulling back the canonical original datum gives the canonical datum of the actual pulled-back quotient module. -/
def canonicalSquareIso : (squareFunctor f f' iX iY hf).obj (OrdinaryDatum.Ordinary.baseDatum f P) ≅
    OrdinaryDatum.Ordinary.baseDatum f' ((Scheme.Modules.pullback iY).obj P) :=
  (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso Geometric.KernelLinearization.modulePullbacks
    (f := fun (_ : PUnit.{1}) => f) (f' := fun (_ : PUnit.{1}) => f') (p := iY)
    (α := fun (_ : PUnit.{1}) => PUnit.unit) (p' := fun (_ : PUnit.{1}) => iX) (fun _ => hf)).app P

/-- The compatible original recovery constructs the full descent isomorphism on the square. -/
def pulledIso : OrdinaryDatum.Ordinary.baseDatum f' ((Scheme.Modules.pullback iY).obj P) ≅
    Ordinary.SquareGluing.pulledDatum f f' iX iY hf D :=
  (canonicalSquareIso f f' iX iY hf P).symm ≪≫ (squareFunctor f f' iX iY hf).mapIso (originalIso f D P e he)

/-- The actual recovered source isomorphism on the square. -/
def pulledRecovery : (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback iY).obj P) ≅
    (Scheme.Modules.pullback iX).obj (D.obj PUnit.unit) :=
  DescentComponentIsomorphisms.componentIso Geometric.KernelLinearization.modulePullbacks f' (pulledIso f f' iX iY hf D P e he)

/-- The constructed square recovery has its exact full geometric kernel-pair compatibility. -/
theorem pulledRecovery_compatible :
    (Scheme.Modules.pullback (pullback.fst f' f')).map (pulledRecovery f f' iX iY hf D P e he).hom ≫
      (Geometric.CechInvariant.relationGluing f' (Ordinary.SquareGluing.pulledDatum f f' iX iY hf D)).hom =
    (Cech.MateNormalization.standardGluing f' (pullback.fst f' f') (pullback.snd f' f') pullback.condition).hom.app
      ((Scheme.Modules.pullback iY).obj P) ≫
        (Scheme.Modules.pullback (pullback.snd f' f')).map (pulledRecovery f f' iX iY hf D P e he).hom := by
  have h := (pulledIso f f' iX iY hf D P e he).hom.comm (pullback.snd f' f' ≫ f')
    (i₁ := PUnit.unit) (i₂ := PUnit.unit) (pullback.fst f' f') (pullback.snd f' f') pullback.condition rfl
  change (Scheme.Modules.pullback (pullback.fst f' f')).map (pulledRecovery f f' iX iY hf D P e he).hom ≫
      (Geometric.CechInvariant.relationGluing f' (Ordinary.SquareGluing.pulledDatum f f' iX iY hf D)).hom =
    (Geometric.CechInvariant.relationGluing f' (OrdinaryDatum.Ordinary.baseDatum f' ((Scheme.Modules.pullback iY).obj P))).hom ≫
      (Scheme.Modules.pullback (pullback.snd f' f')).map (pulledRecovery f f' iX iY hf D P e he).hom at h
  rw [OrdinaryDatum.Ordinary.baseDatum_gluing] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.SquareDescent
