import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineModuleDescent
import OAI.AlgebraicGeometry.Picard.Homomorphisms.IntrinsicModuleDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechEffectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Affine Intrinsic Line Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: effective affine descent of native line-bundle gluing

The supplied datum consists only of the actual pullback module, gluing
maps and cocycle identities. Its descended line bundle is constructed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.Homomorphisms.IntrinsicModuleDescent.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

universe u

/-- Native module-sheaf gluing gives ordinary pseudofunctor descent data. -/
def nativeToDescentData {X Y : Scheme.{u}} {f : X ⟶ Y} (D : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f) :
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f) where
  obj _ := D.module
  hom := fun {_T} q {_i _j} x y hx hy => D.hom q x y hx hy
  hom_self := fun {_T} q {_i} x hx => D.hom_self q x hx
  hom_comp := fun {_T} q {_i _j _k} x y z hx hy hz => D.hom_comp q x y z hx hy hz
  pullHom_hom := fun {_T' _T} t q q' hq {_i _j} x y hx hy x' y' hx' hy' => by
    subst q'
    subst x'
    subst y'
    have he := Picard.PoincareBundle.Geometric.PullHom.pullHom_eq (D.hom q x y hx hy) t (t ≫ x) (t ≫ y) rfl rfl
    simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl] at he
    exact he.trans (D.hom_pullback t q x y hx hy)

variable {R S : CommRingCat.{u}} (f : R ⟶ S)
    (D : Picard.PoincareBundle.Geometric.CocycleDescent.RingMapDatum f) (hf : f.hom.FaithfullyFlat)

/-- Effective descent of geometric Cech gluing produces an invertible
module without a noetherian hypothesis. -/
theorem affineCech_baseModule_invertible :
    Module.Invertible R (Picard.PoincareBundle.Geometric.CechRecovery.baseModule f D hf) := by
  have : Module.Invertible S
      (Picard.PoincareBundle.CocycleEffectiveDescent.moduleDatum f.hom
        (Picard.PoincareBundle.Geometric.CechRecovery.sectionModule f D) (Picard.PoincareBundle.Geometric.CechRecovery.moduleCech f D)).A :=
    Picard.PoincareBundle.Affine.Classification.globalSections_invertible (Picard.PoincareBundle.Geometric.CechRecovery.originalLine f D)
  exact LineModuleDescent.Construction.LineDescent.descendedModule_invertible f.hom hf
    (Picard.PoincareBundle.CocycleEffectiveDescent.moduleDatum f.hom
      (Picard.PoincareBundle.Geometric.CechRecovery.sectionModule f D) (Picard.PoincareBundle.Geometric.CechRecovery.moduleCech f D))

include hf in
/-- The actual equalizer sheaf of geometric Cech invariants is a line
bundle over any affine base. -/
theorem affineCech_invariant_isLine :
    Picard.PoincareBundle.Line.Bundles.IsLine (Picard.PoincareBundle.Affine.CechInvariantMaps.invariant f D) := by
  have := affineCech_baseModule_invertible f D hf
  exact (Picard.PoincareBundle.TildePullback.isLine_tilde_of_invertible
    (Picard.PoincareBundle.Geometric.CechRecovery.baseModule f D hf)).of_iso
      (Picard.PoincareBundle.Affine.CechEffectivity.invariantIso f D hf)

/-- The line bundle constructed from the actual recovered module. -/
def affineCechLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Spec R) where
  sheaf := (tilde.functor R).obj (Picard.PoincareBundle.Geometric.CechRecovery.baseModule f D hf)
  locallyTrivial := by
    have := affineCech_baseModule_invertible f D hf
    exact Picard.PoincareBundle.TildePullback.isLine_tilde_of_invertible (Picard.PoincareBundle.Geometric.CechRecovery.baseModule f D hf)

/-- Its actual pullback is the original line bundle. -/
def affineCechLinePullbackIso :
    (Scheme.Modules.pullback (Spec.map f)).obj (affineCechLine f D hf).sheaf ≅
      (Picard.PoincareBundle.Geometric.CechRecovery.originalLine f D).sheaf :=
  Picard.PoincareBundle.Geometric.CechRecovery.recoveryIso f D hf

/-- Recovery retains the original geometric overlap equation. -/
theorem affineCechLinePullbackIso_compatible :
    Picard.PoincareBundle.Geometric.CechMorphismCoordinates.Compatible f D
      (affineCechLinePullbackIso f D hf).hom :=
  Picard.PoincareBundle.Affine.CechEffectivity.recovery_compatible f D hf

/-- Ordinary native descent data with a line on the cover are effective
over an arbitrary faithfully flat affine ring map. -/
def affineNativeLine (N : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent (Spec.map f))
    (hN : Picard.PoincareBundle.Line.Bundles.IsLine N.module) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Spec R) :=
  affineCechLine f (Picard.PoincareBundle.Ordinary.AffineDescent.ringMapGeometricDatum f (nativeToDescentData N) hN) hf

/-- The recovered native line has exactly the original pullback module. -/
def affineNativeLinePullbackIso (N : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent (Spec.map f))
    (hN : Picard.PoincareBundle.Line.Bundles.IsLine N.module) :
    (Scheme.Modules.pullback (Spec.map f)).obj (affineNativeLine f hf N hN).sheaf ≅ N.module :=
  affineCechLinePullbackIso f
    (Picard.PoincareBundle.Ordinary.AffineDescent.ringMapGeometricDatum f (nativeToDescentData N) hN) hf

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent
