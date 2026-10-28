import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArbitraryAffineLineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

/-! # Arbitrary Global Line Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArbitraryGlobalLineDescent.Construction

noncomputable section

/-! Ordinary geometric line-bundle descent is effective along affine
faithfully flat morphisms over arbitrary schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
  (hD : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit))

include hD in
theorem arbitrary_affineSchemeInvariant_isLine [IsAffine X] [IsAffine Y] [Flat f] [Surjective f] :
    Picard.PoincareBundle.Line.Bundles.IsLine (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryInvariantSheaf f D) := by
  let w := (Scheme.isoSpec_inv_naturality f).symm
  let D' := Picard.PoincareBundle.Ordinary.SquareGluing.pulledDatum f (Spec.map f.appTop) X.isoSpec.inv Y.isoSpec.inv w D
  have hD' : Picard.PoincareBundle.Line.Bundles.IsLine (D'.obj PUnit.unit) := hD.pullback X.isoSpec.inv
  have hpre : f ⁻¹ᵁ Y.isoSpec.inv.opensRange ≤ X.isoSpec.inv.opensRange := by
    simp [Scheme.Hom.opensRange_of_isIso]
  have hff : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  have hl := ArbitraryAffineLineDescent.Construction.arbitrary_ordinaryAffineInvariant_isLine f.appTop D' hD' hff
  apply Picard.PoincareBundle.IsoDescent.isLine_of_pullback Y.isoSpec.symm
  exact hl.of_iso ((Picard.PoincareBundle.Ordinary.KernelPairRestriction.invariantIso f (Spec.map f.appTop)
    X.isoSpec.inv Y.isoSpec.inv w hpre D).symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback Y.isoSpec.inv).app _)

include hD in
theorem arbitrary_ordinaryInvariant_isLine [IsAffineHom f] [Flat f] [Surjective f] :
    Picard.PoincareBundle.Line.Bundles.IsLine (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryInvariantSheaf f D) := by
  apply Picard.PoincareBundle.Line.Locality.isLine_of_locally_isLine
  intro y
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U : X.Opens) := hU.preimage f
  have : Surjective (f ∣_ U) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f U).flip (inferInstanceAs (Surjective f))
  have hD' : Picard.PoincareBundle.Line.Bundles.IsLine ((Picard.PoincareBundle.Ordinary.GlobalLineDescent.openDatum f D U).obj PUnit.unit) :=
    hD.pullback (f ⁻¹ᵁ U).ι
  have hl := arbitrary_affineSchemeInvariant_isLine (f ∣_ U) (Picard.PoincareBundle.Ordinary.GlobalLineDescent.openDatum f D U) hD'
  exact ⟨U, hy, hl.of_iso ((Picard.PoincareBundle.Ordinary.GlobalLineDescent.invariantOpenIso f D U).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _)⟩

def arbitraryDescendedLine [IsAffineHom f] [Flat f] [Surjective f] : Picard.PoincareBundle.Line.Bundles.LineBundle Y :=
  ⟨Picard.PoincareBundle.Geometric.CechInvariant.ordinaryInvariantSheaf f D, arbitrary_ordinaryInvariant_isLine f D hD⟩

def arbitraryDescendedLinePullbackIso [IsAffineHom f] [Flat f] [Surjective f] :
    (Scheme.Modules.pullback f).obj (arbitraryDescendedLine f D hD).sheaf ≅ D.obj PUnit.unit := by
  have ha : IsIso (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryComparison f D) := Picard.PoincareBundle.Ordinary.GlobalLineDescent.comparison_isIso f D hD
  exact @asIso _ _ _ _ (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryComparison f D) ha

theorem arbitraryDescendedLinePullbackIso_compatible [IsAffineHom f] [Flat f] [Surjective f] :
    (Scheme.Modules.pullback (pullback.fst f f)).map (arbitraryDescendedLinePullbackIso f D hD).hom ≫
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D).hom =
    (Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).hom.app (arbitraryDescendedLine f D hD).sheaf ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map (arbitraryDescendedLinePullbackIso f D hD).hom :=
  Picard.PoincareBundle.Cech.MateNormalization.comparison_standard_compatible f (pullback.fst f f) (pullback.snd f f)
    pullback.condition (D.obj PUnit.unit) (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArbitraryGlobalLineDescent.Construction
