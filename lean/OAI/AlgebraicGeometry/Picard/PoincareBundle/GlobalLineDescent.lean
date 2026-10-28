import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Invariant
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsoDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.Descent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Locality
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Global Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalLineDescent

noncomputable section

/-!
# Global geometric line-bundle invariants for PoincareBundle

The invariant sheaf of a geometric line-bundle coaction is locally free
of rank one under a faithfully flat affine morphism to a locally
noetherian scheme. Affine computations are transported through actual
scheme isomorphisms and then applied on an affine open cover.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The invariant pullback comparison is invertible on arbitrary affine schemes. -/
theorem affine_invariantComparison_isIso [IsAffine X] [IsAffine Y] [Flat f]
    (D : BeckDescent.SheafDatum f) (hD : Line.Bundles.IsLine D.A) :
    IsIso (BeckDescent.invariantComparison f D).f := by
  let w := Scheme.isoSpec_inv_naturality f
  let D' := (IsoDescent.transportDatum f (Spec.map f.appTop)
    X.isoSpec.symm Y.isoSpec.symm w).obj D
  have hD' : Line.Bundles.IsLine D'.A := hD.pullback X.isoSpec.inv
  have : D'.A.IsQuasicoherent := QuasiCoherent.isQuasicoherent_of_isLine D'.A hD'
  exact IsoDescent.comparison_isIso_of_transport f (Spec.map f.appTop)
    X.isoSpec.symm Y.isoSpec.symm w D
    (PoincareBundle.Affine.Invariant.invariantComparison_isIso f.appTop D' f.flat_appTop)

/-- The invariant sheaf is a line bundle on arbitrary affine schemes. -/
theorem affine_invariantSheaf_isLine [IsAffine X] [IsAffine Y]
    [IsLocallyNoetherian Y] [Flat f] [Surjective f]
    (D : BeckDescent.SheafDatum f) (hD : Line.Bundles.IsLine D.A) :
    Line.Bundles.IsLine (BeckDescent.invariantSheaf f D) := by
  let w := Scheme.isoSpec_inv_naturality f
  let D' := (IsoDescent.transportDatum f (Spec.map f.appTop)
    X.isoSpec.symm Y.isoSpec.symm w).obj D
  have hD' : Line.Bundles.IsLine D'.A := hD.pullback X.isoSpec.inv
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have hf : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  have hline := PoincareBundle.Affine.Invariant.invariantSheaf_isLine f.appTop D' hf hD'
  apply IsoDescent.isLine_of_pullback Y.isoSpec.symm
  exact hline.of_iso (IsoDescent.invariantSheafIso f (Spec.map f.appTop)
    X.isoSpec.symm Y.isoSpec.symm w D).symm

/-- The invariant sheaf of a line-bundle coaction is itself a line bundle
for faithfully flat affine morphisms over a locally noetherian base. -/
theorem invariantSheaf_isLine [IsAffineHom f] [IsLocallyNoetherian Y]
    [Flat f] [Surjective f]
    (D : BeckDescent.SheafDatum f) (hD : Line.Bundles.IsLine D.A) :
    Line.Bundles.IsLine (BeckDescent.invariantSheaf f D) := by
  apply Line.Locality.isLine_of_locally_isLine
  intro y
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U : X.Opens) := hU.preimage f
  have : Surjective (f ∣_ U) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f U).flip (inferInstanceAs (Surjective f))
  let D' := (Open.Descent.restrictDatum f U).obj D
  have hD' : Line.Bundles.IsLine D'.A := Open.Descent.restrictDatum_isLine f U D hD
  have hline := affine_invariantSheaf_isLine (f ∣_ U) D' hD'
  refine ⟨U, hy, ?_⟩
  exact hline.of_iso ((Open.Descent.invariantSheafRestrictIso f U D).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _)

/-- The globally defined line bundle obtained by taking geometric invariants. -/
def descendedLineBundle [IsAffineHom f] [IsLocallyNoetherian Y] [Flat f] [Surjective f]
    (D : BeckDescent.SheafDatum f) (hD : Line.Bundles.IsLine D.A) :
    Line.Bundles.LineBundle Y :=
  ⟨BeckDescent.invariantSheaf f D, invariantSheaf_isLine f D hD⟩

/-- For a flat affine morphism, the globally defined invariant comparison
recovers every geometric line-bundle coaction. -/
theorem invariantComparison_isIso [IsAffineHom f] [Flat f]
    (D : BeckDescent.SheafDatum f) (hD : Line.Bundles.IsLine D.A) :
    IsIso (BeckDescent.invariantComparison f D).f := by
  apply ModuleLocality.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U : X.Opens) := hU.preimage f
  let D' := (Open.Descent.restrictDatum f U).obj D
  have hD' : Line.Bundles.IsLine D'.A := Open.Descent.restrictDatum_isLine f U D hD
  have hc : IsIso (BeckDescent.invariantComparison (f ∣_ U) D').f :=
    affine_invariantComparison_isIso (f ∣_ U) D' hD'
  have := ModuleLocality.restrict_preservesFiniteLimits U.ι
  have := Open.Adjunction.rightMate_isIso f U
  refine ⟨f ⁻¹ᵁ U, hx, ?_⟩
  exact @InvariantComparison.comparison_map_isIso _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
    (Open.Adjunction.adjointPullbackSquare f U)
    inferInstance inferInstance inferInstance inferInstance D hc

/-- Pullback of the constructed global line bundle is the original line bundle. -/
def descendedLineBundlePullbackIso [IsAffineHom f] [IsLocallyNoetherian Y]
    [Flat f] [Surjective f]
    (D : BeckDescent.SheafDatum f) (hD : Line.Bundles.IsLine D.A) :
    (Scheme.Modules.pullback f).obj (descendedLineBundle f D hD).sheaf ≅ D.A := by
  let a := (BeckDescent.invariantComparison f D).f
  have ha : IsIso a := invariantComparison_isIso f D hD
  exact @asIso _ _ _ _ a ha

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalLineDescent
