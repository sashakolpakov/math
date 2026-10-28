import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Polarized Objects -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PolarizedObjects

noncomputable section

/-!
Polarized full-level objects with an actual closed embedding into a fixed
ambient scheme after base change to a test scheme.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (P : Over S)

/-- The product-based test ambient is the ordinary base change of the larger test ambient. -/
def embeddedFamilyAmbientBaseChangeIso {T U : Over S} (f : T ⟶ U) :
    (Over.pullback f.left).obj (FamilyFunctor.embeddedFamilyAmbient P U) ≅ FamilyFunctor.embeddedFamilyAmbient P T := by
  let h := FamilyFunctor.embeddedFamilyAmbient_isPullback P f
  exact Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd

/-- An embedded object retains all polarization and ordered full-level data. -/
structure EmbeddedPolarizedObject (g : ℕ) (δ : Fin g → ℕ) (N : ℕ) (T : Over S) where
  object : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left
  embedding : object.abelian.scheme ⟶ FamilyFunctor.embeddedFamilyAmbient P T
  closedImmersion : IsClosedImmersion embedding.left

attribute [instance] EmbeddedPolarizedObject.closedImmersion

namespace EmbeddedPolarizedObject

variable {P} {g N : ℕ} {δ : Fin g → ℕ} {T U : Over S}

/-- Forgetting the additional structures gives the actual ideal-sheaf family. -/
def closedFamily (A : EmbeddedPolarizedObject P g δ N T) :
    Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P T) :=
  Closed.Families.FlatClosedFamily.ofEmbedding A.embedding

/-- Pull back both the moduli data and its embedding along a map of test schemes. -/
def pullback (A : EmbeddedPolarizedObject P g δ N U) (f : T ⟶ U) :
    EmbeddedPolarizedObject P g δ N T where
  object := A.object.pullback f.left
  embedding := (Over.pullback f.left).map A.embedding ≫ (embeddedFamilyAmbientBaseChangeIso P f).hom
  closedImmersion := by
    have he : IsClosedImmersion ((Over.pullback f.left).map A.embedding).left :=
      MorphismProperty.overPullbackMap f.left A.embedding A.closedImmersion
    have hi : IsIso (embeddedFamilyAmbientBaseChangeIso P f).hom.left :=
      inferInstanceAs (IsIso ((Over.forget T.left).map (embeddedFamilyAmbientBaseChangeIso P f).hom))
    exact @IsClosedImmersion.comp _ _ _ ((Over.pullback f.left).map A.embedding).left
      (embeddedFamilyAmbientBaseChangeIso P f).hom.left he inferInstance

end EmbeddedPolarizedObject

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PolarizedObjects
