import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DescentOverlapCharts
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicDescentRecovery
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EffectiveLineDescent

/-! # Ordinary Global Line Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.OrdinaryGlobalLineDescent.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: effective ordinary line descent on arbitrary schemes

The input consists of the actual ordinary gluing on the cover. The
invariant line and the compatible recovery isomorphism are constructed
over any affine faithfully flat cover, without a noetherian hypothesis.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

universe u

/-- Ordinary invariant lines over spectra need no noetherian assumption. -/
theorem ordinarySpecInvariant_isLine {R S : CommRingCat.{u}} (g : R ⟶ S)
    (hg : g.hom.FaithfullyFlat)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => Spec.map g))
    (hD : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit)) :
    Picard.PoincareBundle.Line.Bundles.IsLine (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryInvariantSheaf (Spec.map g) D) :=
  (AffineIntrinsicLineDescent.Construction.LineDescent.affineCech_invariant_isLine g (Picard.PoincareBundle.Ordinary.AffineDescent.ringMapGeometricDatum g D hD) hg).of_iso
    (Picard.PoincareBundle.Ordinary.AffineEffectivity.invariantIso g D hD)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The ordinary invariant is a line on arbitrary affine schemes. -/
theorem ordinaryAffineInvariant_isLine [IsAffine X] [IsAffine Y] [Flat f] [Surjective f]
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (hD : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit)) :
    Picard.PoincareBundle.Line.Bundles.IsLine (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryInvariantSheaf f D) := by
  let w := (Scheme.isoSpec_inv_naturality f).symm
  have sq : IsPullback X.isoSpec.inv (Spec.map f.appTop) f Y.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨w⟩
  let D' := DescentOverlapCharts.Construction.LineDescent.openChartDatum f (Spec.map f.appTop) Y.isoSpec.inv X.isoSpec.inv w D
  have hD' : Picard.PoincareBundle.Line.Bundles.IsLine (D'.obj PUnit.unit) := hD.pullback X.isoSpec.inv
  have hf : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  have hl := ordinarySpecInvariant_isLine f.appTop hf D' hD'
  apply Picard.PoincareBundle.IsoDescent.isLine_of_pullback Y.isoSpec.symm
  exact hl.of_iso ((DescentOverlapCharts.Construction.LineDescent.ordinaryInvariantOpenIso f (Spec.map f.appTop) Y.isoSpec.inv X.isoSpec.inv w sq D).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback Y.isoSpec.inv).app _)

/-- Recovery of ordinary invariants is invertible on arbitrary affine schemes. -/
theorem ordinaryAffineComparison_isIso [IsAffine X] [IsAffine Y] [Flat f] [Surjective f]
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (hD : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit)) : IsIso (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryComparison f D) := by
  let w := (Scheme.isoSpec_inv_naturality f).symm
  have sq : IsPullback X.isoSpec.inv (Spec.map f.appTop) f Y.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨w⟩
  let D' := DescentOverlapCharts.Construction.LineDescent.openChartDatum f (Spec.map f.appTop) Y.isoSpec.inv X.isoSpec.inv w D
  have hD' : Picard.PoincareBundle.Line.Bundles.IsLine (D'.obj PUnit.unit) := hD.pullback X.isoSpec.inv
  have hf : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  have hr : IsIso ((Scheme.Modules.restrictFunctor X.isoSpec.inv).map (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryComparison f D)) :=
    (DescentOverlapCharts.Construction.LineDescent.ordinaryComparison_open_isIso_iff f (Spec.map f.appTop) Y.isoSpec.inv X.isoSpec.inv w sq D).mpr
      (Picard.PoincareBundle.Ordinary.AffineEffectivity.comparison_isIso f.appTop D' hD' hf)
  have hp : IsIso ((Scheme.Modules.pullback X.isoSpec.inv).map (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryComparison f D)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.inv)
      (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryComparison f D)).mp hr
  have : (Scheme.Modules.pullback X.isoSpec.inv).IsEquivalence :=
    Picard.PoincareBundle.IsoDescent.pullback_isEquivalence X.isoSpec.symm
  exact isIso_of_reflects_iso (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryComparison f D) (Scheme.Modules.pullback X.isoSpec.inv)

variable [IsAffineHom f] [Flat f] [Surjective f]
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (hD : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit))

include hD in
/-- Ordinary invariants form a genuine line over any target scheme. -/
theorem ordinaryGlobalInvariant_isLine : Picard.PoincareBundle.Line.Bundles.IsLine (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryInvariantSheaf f D) := by
  apply Picard.PoincareBundle.Line.Locality.isLine_of_locally_isLine
  intro y
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U : X.Opens) := hU.preimage f
  have : Surjective (f ∣_ U) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f U).flip (inferInstanceAs (Surjective f))
  let w := (morphismRestrict_ι f U).symm
  let D' := DescentOverlapCharts.Construction.LineDescent.openChartDatum f (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι w D
  have hD' : Picard.PoincareBundle.Line.Bundles.IsLine (D'.obj PUnit.unit) := hD.pullback (f ⁻¹ᵁ U).ι
  have hl := ordinaryAffineInvariant_isLine (f ∣_ U) D' hD'
  refine ⟨U, hy, ?_⟩
  exact hl.of_iso ((DescentOverlapCharts.Construction.LineDescent.ordinaryInvariantOpenIso f (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι w
    (isPullback_morphismRestrict f U).flip D).symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _)

include hD in
/-- The constructed global invariant recovers the original line by its canonical map. -/
theorem ordinaryGlobalComparison_isIso : IsIso (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryComparison f D) := by
  apply Picard.PoincareBundle.ModuleLocality.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U : X.Opens) := hU.preimage f
  have : Surjective (f ∣_ U) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f U).flip (inferInstanceAs (Surjective f))
  let w := (morphismRestrict_ι f U).symm
  let D' := DescentOverlapCharts.Construction.LineDescent.openChartDatum f (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι w D
  have hD' : Picard.PoincareBundle.Line.Bundles.IsLine (D'.obj PUnit.unit) := hD.pullback (f ⁻¹ᵁ U).ι
  refine ⟨f ⁻¹ᵁ U, hx, ?_⟩
  exact (DescentOverlapCharts.Construction.LineDescent.ordinaryComparison_open_isIso_iff f (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι w
    (isPullback_morphismRestrict f U).flip D).mpr (ordinaryAffineComparison_isIso (f ∣_ U) D' hD')

variable (N : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N.module)

/-- A genuine line bundle constructed from arbitrary ordinary native line gluing. -/
def nativeDescendedLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y where
  sheaf := IntrinsicInvariantDescent.Construction.LineDescent.nativeInvariant f N
  locallyTrivial := ordinaryGlobalInvariant_isLine f (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData N) hN

/-- The canonical recovery isomorphism on the original covering scheme. -/
def nativeDescendedLinePullbackIso :
    (Scheme.Modules.pullback f).obj (nativeDescendedLine f N hN).sheaf ≅ N.module :=
  @asIso _ _ _ _ (IntrinsicInvariantDescent.Construction.LineDescent.nativeInvariantComparison f N)
    (ordinaryGlobalComparison_isIso f (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData N) hN)

/-- The canonical recovery retains every native gluing equation. -/
theorem nativeDescendedLinePullbackIso_compatible {T : Scheme.{u}} (q : T ⟶ Y)
    (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f (nativeDescendedLine f N hN).sheaf) N
      (nativeDescendedLinePullbackIso f N hN).hom q x y hx hy :=
  IntrinsicInvariantDescent.Construction.LineDescent.nativeInvariantComparison_compatible f N q x y hx hy

/-- The actual global line recovers all the original ordinary descent data. -/
def nativeDescendedLineRecoveryIso :
    (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj (nativeDescendedLine f N hN).sheaf ≅
      AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData N :=
  IntrinsicDescentRecovery.Construction.LineDescent.nativeRecoveryIso f (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData N) _ (nativeDescendedLinePullbackIso f N hN)
    (IntrinsicInvariantDescent.Construction.LineDescent.nativeInvariantComparison_compatible f N)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.OrdinaryGlobalLineDescent.Construction.LineDescent
