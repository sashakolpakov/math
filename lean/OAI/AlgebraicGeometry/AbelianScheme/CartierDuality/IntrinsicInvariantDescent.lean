import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DescentRelationMorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineEffectivity
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantUniversal

/-! # Intrinsic Invariant Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicInvariantDescent.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: ordinary invariant lines and their full native recovery
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (D : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f)

/-- The actual equalizer sheaf defined by the supplied ordinary gluing. -/
def nativeInvariant : Y.Modules :=
  Picard.PoincareBundle.Geometric.CechInvariant.ordinaryInvariantSheaf f (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData D)

/-- The canonical pullback comparison from ordinary invariants. -/
def nativeInvariantComparison :
    (Scheme.Modules.pullback f).obj (nativeInvariant f D) ⟶ D.module :=
  Picard.PoincareBundle.Geometric.CechInvariant.ordinaryComparison f (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData D)

/-- The invariant comparison preserves the given gluing on every test scheme. -/
theorem nativeInvariantComparison_compatible {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f (nativeInvariant f D)) D
      (nativeInvariantComparison f D) q x y hx hy := by
  apply DescentRelationMorphisms.Construction.LineDescent.compatible_of_overlap
  unfold DescentRelationMorphisms.Construction.LineDescent.CompatibleAt
  rw [DescentRelationMorphisms.Construction.LineDescent.canonicalDescent_standard]
  exact Picard.PoincareBundle.Cech.MateNormalization.comparison_standard_compatible f
    (pullback.fst f f) (pullback.snd f f) pullback.condition D.module
    (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData D))

/-- Full native compatibility gives a unique map to the actual invariant sheaf. -/
theorem nativeInvariant_existsUnique (L : Y.Modules)
    (b : (Scheme.Modules.pullback f).obj L ⟶ D.module)
    (hb : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L) D b q x y hx hy) :
    ∃! a : L ⟶ nativeInvariant f D,
      (Scheme.Modules.pullback f).map a ≫ nativeInvariantComparison f D = b := by
  have h := hb (pullback.snd f f ≫ f) (pullback.fst f f) (pullback.snd f f)
    pullback.condition rfl
  unfold DescentRelationMorphisms.Construction.LineDescent.CompatibleAt at h
  rw [DescentRelationMorphisms.Construction.LineDescent.canonicalDescent_standard] at h
  exact Picard.PoincareBundle.Cech.InvariantUniversal.existsUnique_lift f
    (pullback.fst f f) (pullback.snd f f) pullback.condition D.module
    (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData D)) L ⟨b, h⟩

variable {R S : CommRingCat.{u}} (g : R ⟶ S) (hg : g.hom.FaithfullyFlat)
    (N : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent (Spec.map g)) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N.module)

include hg hN in
/-- Ordinary invariants form a line over any faithfully flat affine base. -/
theorem affine_nativeInvariant_isLine : Picard.PoincareBundle.Line.Bundles.IsLine (nativeInvariant (Spec.map g) N) :=
  (AffineIntrinsicLineDescent.Construction.LineDescent.affineCech_invariant_isLine g
    (Picard.PoincareBundle.Ordinary.AffineDescent.ringMapGeometricDatum g (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData N) hN) hg).of_iso
      (Picard.PoincareBundle.Ordinary.AffineEffectivity.invariantIso g (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData N) hN)

include hg hN in
/-- The actual ordinary invariant comparison is invertible without a noetherian hypothesis. -/
theorem affine_nativeInvariantComparison_isIso : IsIso (nativeInvariantComparison (Spec.map g) N) :=
  Picard.PoincareBundle.Ordinary.AffineEffectivity.comparison_isIso g (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData N) hN hg

/-- The actual ordinary invariant line on an affine base. -/
def affineNativeInvariantLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Spec R) where
  sheaf := nativeInvariant (Spec.map g) N
  locallyTrivial := affine_nativeInvariant_isLine g hg N hN

/-- Recovery of the original native line, using the invariant comparison itself. -/
def affineNativeInvariantPullbackIso :
    (Scheme.Modules.pullback (Spec.map g)).obj (affineNativeInvariantLine g hg N hN).sheaf ≅
      N.module := by
  exact @asIso _ _ _ _ (nativeInvariantComparison (Spec.map g) N)
    (affine_nativeInvariantComparison_isIso g hg N hN)

/-- The recovered line retains the supplied gluing on every scheme, including nonreduced tests. -/
theorem affineNativeInvariantPullbackIso_compatible {T : Scheme.{u}} (q : T ⟶ Spec R)
    (x y : T ⟶ Spec S) (hx : x ≫ Spec.map g = q) (hy : y ≫ Spec.map g = q) :
    DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (Spec.map g) (affineNativeInvariantLine g hg N hN).sheaf) N
      (affineNativeInvariantPullbackIso g hg N hN).hom q x y hx hy :=
  nativeInvariantComparison_compatible (Spec.map g) N q x y hx hy

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicInvariantDescent.Construction.LineDescent
