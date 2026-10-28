import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.KernelPairRestriction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineEffectivity
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsoDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Affine Scheme Effectivity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineSchemeEffectivity

noncomputable section

/-!
# Ordinary geometric descent is effective on arbitrary affine schemes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y] [Flat f] [Surjective f]
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
  (hD : Line.Bundles.IsLine (D.obj PUnit.unit))

include hD in
/-- The actual ordinary invariant comparison is invertible on any faithfully flat affine map. -/
theorem comparison_isIso : IsIso (Geometric.CechInvariant.ordinaryComparison f D) := by
  let w := (Scheme.isoSpec_inv_naturality f).symm
  let D' := SquareGluing.pulledDatum f (Spec.map f.appTop) X.isoSpec.inv Y.isoSpec.inv w D
  have hD' : Line.Bundles.IsLine (D'.obj PUnit.unit) := hD.pullback X.isoSpec.inv
  have hpre : f ⁻¹ᵁ Y.isoSpec.inv.opensRange ≤ X.isoSpec.inv.opensRange := by
    simp [Scheme.Hom.opensRange_of_isIso]
  have hff : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  have hc := AffineEffectivity.comparison_isIso f.appTop D' hD' hff
  have hr := (KernelPairRestriction.comparison_restrict_isIso_iff f (Spec.map f.appTop)
    X.isoSpec.inv Y.isoSpec.inv w hpre D).mpr hc
  have : IsIso ((Scheme.Modules.pullback X.isoSpec.inv).map (Geometric.CechInvariant.ordinaryComparison f D)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.inv) _).mp hr
  have : (Scheme.Modules.pullback X.isoSpec.inv).IsEquivalence :=
    IsoDescent.pullback_isEquivalence X.isoSpec.symm
  exact isIso_of_reflects_iso (Geometric.CechInvariant.ordinaryComparison f D) (Scheme.Modules.pullback X.isoSpec.inv)

include hD in
/-- Over a locally noetherian affine base, the actual ordinary invariant is a line bundle. -/
theorem invariant_isLine [IsLocallyNoetherian Y] : Line.Bundles.IsLine (Geometric.CechInvariant.ordinaryInvariantSheaf f D) := by
  let w := (Scheme.isoSpec_inv_naturality f).symm
  let D' := SquareGluing.pulledDatum f (Spec.map f.appTop) X.isoSpec.inv Y.isoSpec.inv w D
  have hD' : Line.Bundles.IsLine (D'.obj PUnit.unit) := hD.pullback X.isoSpec.inv
  have hpre : f ⁻¹ᵁ Y.isoSpec.inv.opensRange ≤ X.isoSpec.inv.opensRange := by
    simp [Scheme.Hom.opensRange_of_isIso]
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have hff : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  have hl := AffineEffectivity.invariant_isLine f.appTop D' hD' hff
  apply IsoDescent.isLine_of_pullback Y.isoSpec.symm
  exact hl.of_iso ((KernelPairRestriction.invariantIso f (Spec.map f.appTop)
    X.isoSpec.inv Y.isoSpec.inv w hpre D).symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback Y.isoSpec.inv).app _)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineSchemeEffectivity
