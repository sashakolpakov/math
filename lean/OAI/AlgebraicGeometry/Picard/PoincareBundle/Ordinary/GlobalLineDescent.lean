import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineSchemeEffectivity
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Locality
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Global Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

noncomputable section

/-!
# Effective global line-bundle descent from ordinary geometric Čech data

The descended sheaf is the globally defined equalizer on the actual scheme kernel pair.
The input consists of an ordinary geometric descent datum and a line bundle on the cover;
no comonad coaction or effectivity hypothesis is supplied.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))

/-- The actual ordinary descent datum on the inverse image of a base open. -/
def openDatum (U : Y.Opens) : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f ∣_ U) :=
  SquareGluing.pulledDatum f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι (morphismRestrict_ι f U).symm D

/-- The globally defined ordinary invariant restricts to the invariant on every base open. -/
def invariantOpenIso (U : Y.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj (Geometric.CechInvariant.ordinaryInvariantSheaf f D) ≅
      Geometric.CechInvariant.ordinaryInvariantSheaf (f ∣_ U) (openDatum f D U) :=
  KernelPairRestriction.invariantIso f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι
    (morphismRestrict_ι f U).symm (by simp only [Scheme.Opens.opensRange_ι]; exact le_rfl) D

/-- The actual ordinary invariant comparison is detected on the corresponding restricted datum. -/
theorem comparison_open_isIso_iff (U : Y.Opens) :
    IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (Geometric.CechInvariant.ordinaryComparison f D)) ↔
      IsIso (Geometric.CechInvariant.ordinaryComparison (f ∣_ U) (openDatum f D U)) :=
  KernelPairRestriction.comparison_restrict_isIso_iff f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι
    (morphismRestrict_ι f U).symm (by simp only [Scheme.Opens.opensRange_ι]; exact le_rfl) D

variable (hD : Line.Bundles.IsLine (D.obj PUnit.unit))

include hD in
/-- Faithfully flat affine morphisms effectively descend the original ordinary geometric line datum. -/
theorem comparison_isIso [IsAffineHom f] [Flat f] [Surjective f] : IsIso (Geometric.CechInvariant.ordinaryComparison f D) := by
  apply ModuleLocality.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U : X.Opens) := hU.preimage f
  have : Surjective (f ∣_ U) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f U).flip (inferInstanceAs (Surjective f))
  have hD' : Line.Bundles.IsLine ((openDatum f D U).obj PUnit.unit) := hD.pullback (f ⁻¹ᵁ U).ι
  have hc := AffineSchemeEffectivity.comparison_isIso (f ∣_ U) (openDatum f D U) hD'
  exact ⟨f ⁻¹ᵁ U, hx, (comparison_open_isIso_iff f D U).mpr hc⟩

include hD in
/-- The actual global ordinary invariant is a line bundle over a locally noetherian base. -/
theorem invariant_isLine [IsAffineHom f] [IsLocallyNoetherian Y] [Flat f] [Surjective f] :
    Line.Bundles.IsLine (Geometric.CechInvariant.ordinaryInvariantSheaf f D) := by
  apply Line.Locality.isLine_of_locally_isLine
  intro y
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U : X.Opens) := hU.preimage f
  have : Surjective (f ∣_ U) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f U).flip (inferInstanceAs (Surjective f))
  have hD' : Line.Bundles.IsLine ((openDatum f D U).obj PUnit.unit) := hD.pullback (f ⁻¹ᵁ U).ι
  have hl := AffineSchemeEffectivity.invariant_isLine (f ∣_ U) (openDatum f D U) hD'
  exact ⟨U, hy, hl.of_iso ((invariantOpenIso f D U).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _)⟩

/-- The descended line bundle is the actual globally defined ordinary invariant sheaf. -/
def descendedLine [IsAffineHom f] [IsLocallyNoetherian Y] [Flat f] [Surjective f] :
    Line.Bundles.LineBundle Y :=
  ⟨Geometric.CechInvariant.ordinaryInvariantSheaf f D, invariant_isLine f D hD⟩

/-- The actual canonical invariant comparison recovers the original line bundle on the cover. -/
def descendedLinePullbackIso [IsAffineHom f] [IsLocallyNoetherian Y] [Flat f] [Surjective f] :
    (Scheme.Modules.pullback f).obj (descendedLine f D hD).sheaf ≅ D.obj PUnit.unit := by
  have ha : IsIso (Geometric.CechInvariant.ordinaryComparison f D) := comparison_isIso f D hD
  exact @asIso _ _ _ _ (Geometric.CechInvariant.ordinaryComparison f D) ha

/-- Recovery respects the original geometric gluing on the scheme-theoretic kernel pair. -/
theorem descendedLinePullbackIso_compatible [IsAffineHom f] [IsLocallyNoetherian Y] [Flat f] [Surjective f] :
    (Scheme.Modules.pullback (pullback.fst f f)).map (descendedLinePullbackIso f D hD).hom ≫
      (Geometric.CechInvariant.relationGluing f D).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).hom.app (descendedLine f D hD).sheaf ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map (descendedLinePullbackIso f D hD).hom :=
  Cech.MateNormalization.comparison_standard_compatible f (pullback.fst f f) (pullback.snd f f)
    pullback.condition (D.obj PUnit.unit) (Geometric.CechInvariant.relationGluing f D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent
