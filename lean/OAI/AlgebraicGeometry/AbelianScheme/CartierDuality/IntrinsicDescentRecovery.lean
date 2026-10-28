import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicInvariantDescent

/-! # Intrinsic Descent Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicDescentRecovery.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: recovery as an isomorphism of all ordinary descent data
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The one-object index is handled before instantiating the descent objects. -/
def nativeDatumIso
    (D E : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : D.obj PUnit.unit ≅ E.obj PUnit.unit)
    (he : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D)
        (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f E) e.hom q x y hx hy) : D ≅ E :=
  Pseudofunctor.DescentData.isoMk (fun i => by cases i; exact e)
    (fun {_T} q {i j} x y hx hy => by cases i; cases j; exact he q x y hx hy)

/-- A compatible recovery isomorphism recovers the entire ordinary datum. -/
def nativeRecoveryIso
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f)) (L : Y.Modules)
    (e : (Scheme.Modules.pullback f).obj L ≅ D.obj PUnit.unit)
    (he : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L) (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D)
        e.hom q x y hx hy) :
    (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ≅ D :=
  nativeDatumIso f _ D e he

variable {R S : CommRingCat.{u}} (g : R ⟶ S) (hg : g.hom.FaithfullyFlat)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => Spec.map g))
    (hD : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit))

/-- The affine invariant construction recovers the whole ordinary gluing datum. -/
def affineOrdinaryRecoveryIso :
    (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => Spec.map g)).obj
      (IntrinsicInvariantDescent.Construction.LineDescent.affineNativeInvariantLine g hg (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor (Spec.map g) D) hD).sheaf ≅
        D :=
  nativeRecoveryIso (Spec.map g) D _
    (IntrinsicInvariantDescent.Construction.LineDescent.affineNativeInvariantPullbackIso g hg (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor (Spec.map g) D) hD)
    (IntrinsicInvariantDescent.Construction.LineDescent.affineNativeInvariantPullbackIso_compatible g hg
      (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor (Spec.map g) D) hD)

variable [IsAffine X] [IsAffine Y]

/-- The actual affine coordinate square induces an equivalence of full descent categories. -/
def affineCoordinateDescentEquivalence :
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f) ≌
      Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => Spec.map f.appTop) :=
  Pseudofunctor.DescentData.pullFunctorEquivalence Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks Y.isoSpec.symm
    (α := id) (p' := fun _ => X.isoSpec.inv)
    (fun _ => (Scheme.isoSpec_inv_naturality f).symm)
    (β := id) (q' := fun _ => X.isoSpec.hom)
    (fun _ => Scheme.isoSpec_hom_naturality f)

variable [Flat f] [Surjective f]
    (N : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (hN : Picard.PoincareBundle.Line.Bundles.IsLine (N.obj PUnit.unit))

/-- The descended line on an arbitrary affine target, in its native scheme category. -/
def affineOrdinaryLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y := by
  let N' := (affineCoordinateDescentEquivalence f).functor.obj N
  have hN' : Picard.PoincareBundle.Line.Bundles.IsLine (N'.obj PUnit.unit) := hN.pullback X.isoSpec.inv
  have hf : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback Y.isoSpec.hom
    (IntrinsicInvariantDescent.Construction.LineDescent.affineNativeInvariantLine f.appTop hf
      (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor (Spec.map f.appTop) N') hN')

/-- Affine change of coordinates retains every native gluing equation. -/
def affineOrdinaryLineRecoveryIso :
    (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj (affineOrdinaryLine f N hN).sheaf ≅
      N := by
  let E := affineCoordinateDescentEquivalence f
  let N' := E.functor.obj N
  have hN' : Picard.PoincareBundle.Line.Bundles.IsLine (N'.obj PUnit.unit) := hN.pullback X.isoSpec.inv
  have hf : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  let L := IntrinsicInvariantDescent.Construction.LineDescent.affineNativeInvariantLine f.appTop hf
    (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor (Spec.map f.appTop) N') hN'
  exact ((Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareComparison (Spec.map f.appTop) f Y.isoSpec.hom X.isoSpec.hom
    (Scheme.isoSpec_hom_naturality f)).app L.sheaf).symm ≪≫
    E.inverse.mapIso (affineOrdinaryRecoveryIso f.appTop hf N' hN') ≪≫ E.unitIso.symm.app N

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicDescentRecovery.Construction.LineDescent
