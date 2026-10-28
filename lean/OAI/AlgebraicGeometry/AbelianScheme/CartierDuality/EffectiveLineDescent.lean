import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineModuleDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalLineDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Effective Line Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EffectiveLineDescent.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: effective geometric line descent over arbitrary bases

Actual invariant module sheaves descend through every affine faithfully
flat morphism. The recovered comparison retains the original coaction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- On arbitrary affine schemes, invariants of a faithfully flat line
coaction are locally free of rank one. -/
theorem affine_invariantSheaf_isLine [IsAffine X] [IsAffine Y] [Flat f] [Surjective f]
    (D : Picard.PoincareBundle.BeckDescent.SheafDatum f) (hD : Picard.PoincareBundle.Line.Bundles.IsLine D.A) :
    Picard.PoincareBundle.Line.Bundles.IsLine (Picard.PoincareBundle.BeckDescent.invariantSheaf f D) := by
  let w := Scheme.isoSpec_inv_naturality f
  let D' := (Picard.PoincareBundle.IsoDescent.transportDatum f (Spec.map f.appTop)
    X.isoSpec.symm Y.isoSpec.symm w).obj D
  have hD' : Picard.PoincareBundle.Line.Bundles.IsLine D'.A := hD.pullback X.isoSpec.inv
  have hf : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  have hline := LineModuleDescent.Construction.LineDescent.invariantSheaf_isLine f.appTop D' hf hD'
  apply Picard.PoincareBundle.IsoDescent.isLine_of_pullback Y.isoSpec.symm
  exact hline.of_iso (Picard.PoincareBundle.IsoDescent.invariantSheafIso f (Spec.map f.appTop)
    X.isoSpec.symm Y.isoSpec.symm w D).symm

/-- Invariants form an actual line bundle over an arbitrary target
scheme, as verified on an affine open cover. -/
theorem geometric_invariantSheaf_isLine [IsAffineHom f] [Flat f] [Surjective f]
    (D : Picard.PoincareBundle.BeckDescent.SheafDatum f) (hD : Picard.PoincareBundle.Line.Bundles.IsLine D.A) :
    Picard.PoincareBundle.Line.Bundles.IsLine (Picard.PoincareBundle.BeckDescent.invariantSheaf f D) := by
  apply Picard.PoincareBundle.Line.Locality.isLine_of_locally_isLine
  intro y
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U : X.Opens) := hU.preimage f
  have : Surjective (f ∣_ U) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f U).flip (inferInstanceAs (Surjective f))
  let D' := (Picard.PoincareBundle.Open.Descent.restrictDatum f U).obj D
  have hD' : Picard.PoincareBundle.Line.Bundles.IsLine D'.A := Picard.PoincareBundle.Open.Descent.restrictDatum_isLine f U D hD
  have hline := affine_invariantSheaf_isLine (f ∣_ U) D' hD'
  refine ⟨U, hy, ?_⟩
  exact hline.of_iso ((Picard.PoincareBundle.Open.Descent.invariantSheafRestrictIso f U D).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _)

/-- The descended object is a line bundle in the same native interface
used by the Poincare and relative Picard constructions. -/
def descendedLineBundle [IsAffineHom f] [Flat f] [Surjective f]
    (D : Picard.PoincareBundle.BeckDescent.SheafDatum f) (hD : Picard.PoincareBundle.Line.Bundles.IsLine D.A) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y where
  sheaf := Picard.PoincareBundle.BeckDescent.invariantSheaf f D
  locallyTrivial := geometric_invariantSheaf_isLine f D hD

/-- Pullback of the constructed line bundle recovers the original
module sheaf by the canonical invariant comparison. -/
def descendedLineBundlePullbackIso [IsAffineHom f] [Flat f] [Surjective f]
    (D : Picard.PoincareBundle.BeckDescent.SheafDatum f) (hD : Picard.PoincareBundle.Line.Bundles.IsLine D.A) :
    (Scheme.Modules.pullback f).obj (descendedLineBundle f D hD).sheaf ≅ D.A := by
  let a := (Picard.PoincareBundle.BeckDescent.invariantComparison f D).f
  have ha : IsIso a := Picard.PoincareBundle.GlobalLineDescent.invariantComparison_isIso f D hD
  exact @asIso _ _ _ _ a ha

/-- The recovery map preserves the original coaction, not just the
isomorphism type of the underlying module. -/
theorem descendedLineBundlePullbackIso_preservesCoaction [IsAffineHom f] [Flat f] [Surjective f]
    (D : Picard.PoincareBundle.BeckDescent.SheafDatum f) (hD : Picard.PoincareBundle.Line.Bundles.IsLine D.A) :
    ((CategoryTheory.Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)).obj
      (descendedLineBundle f D hD).sheaf).a ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).toComonad.map
          (descendedLineBundlePullbackIso f D hD).hom =
      (descendedLineBundlePullbackIso f D hD).hom ≫ D.a :=
  (Picard.PoincareBundle.BeckDescent.invariantComparison f D).h

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EffectiveLineDescent.Construction.LineDescent
