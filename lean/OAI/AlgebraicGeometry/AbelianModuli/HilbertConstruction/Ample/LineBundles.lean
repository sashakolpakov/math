import Mathlib.AlgebraicGeometry.AffineScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers

/-! # Line Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Ampleness of actual line bundles. A section is nonvanishing where its map
from the structure sheaf is locally an isomorphism. Ampleness means that
positive tensor powers have sections with affine nonvanishing neighborhoods
covering the quasi-compact scheme (Stacks Project, Definition 01PR).
Tensor powers are specified by their universal multilinear property.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- Pullback of a section, viewed as a morphism from the structure module. -/
def Ample.LineBundles.pullbackSection {M : Y.Modules} (f : X ⟶ Y) (s : Line.Bundles.structureModule Y ⟶ M) :
    Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M :=
  (Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map s

/-- The largest open on which the section is a local frame. -/
def Ample.LineBundles.sectionNonvanishing {M : X.Modules} (s : Line.Bundles.structureModule X ⟶ M) : X.Opens :=
  sSup {U : X.Opens | IsIso (Ample.LineBundles.pullbackSection U.ι s)}

/-- A globally invertible section is nonvanishing everywhere. -/
theorem Ample.LineBundles.sectionNonvanishing_of_isIso {M : X.Modules} (s : Line.Bundles.structureModule X ⟶ M)
    [IsIso s] : Ample.LineBundles.sectionNonvanishing s = ⊤ := by
  apply top_unique
  apply le_sSup
  change IsIso (Ample.LineBundles.pullbackSection (⊤ : X.Opens).ι s)
  dsimp [Ample.LineBundles.pullbackSection]
  infer_instance

/-- Ampleness via affine nonvanishing loci of sections of positive powers. -/
def Line.Bundles.LineBundle.IsAmple (L : Line.Bundles.LineBundle X) : Prop :=
  IsCompact (Set.univ : Set X) ∧
    ∀ x : X, ∃ (n : ℕ) (_ : 0 < n) (P : Line.Bundles.LineBundle X)
      (_ : Tensor.Powers.IsTensorPower L.sheaf n P.sheaf) (s : Line.Bundles.structureModule X ⟶ P.sheaf),
      x ∈ Ample.LineBundles.sectionNonvanishing s ∧ IsAffineOpen (Ample.LineBundles.sectionNonvanishing s)

/-- The trivial line bundle on an affine scheme is ample. -/
theorem Line.Bundles.LineBundle.trivial_isAmple (X : Scheme.{u}) [IsAffine X] : (Line.Bundles.LineBundle.trivial X).IsAmple := by
  refine ⟨isCompact_univ, fun x => ?_⟩
  refine ⟨1, Nat.zero_lt_one, Line.Bundles.LineBundle.trivial X, Tensor.Powers.isTensorPower_one _, 𝟙 _, ?_, ?_⟩
  · change x ∈ @Ample.LineBundles.sectionNonvanishing X (Line.Bundles.structureModule X) (𝟙 _)
    rw [Ample.LineBundles.sectionNonvanishing_of_isIso]
    trivial
  · change IsAffineOpen (@Ample.LineBundles.sectionNonvanishing X (Line.Bundles.structureModule X) (𝟙 _))
    rw [Ample.LineBundles.sectionNonvanishing_of_isIso]
    exact isAffineOpen_top X

/-- Relative ampleness is ampleness over each affine open of the base. -/
def Line.Bundles.LineBundle.IsRelativelyAmple (L : Line.Bundles.LineBundle X) (f : X ⟶ Y) : Prop :=
  ∀ U : Y.Opens, IsAffineOpen U →
    (Line.Bundles.LineBundle.pullback (f ⁻¹ᵁ U).ι L).IsAmple

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
