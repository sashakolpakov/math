import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.AmbientIsomorphisms

/-! # Ambient Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Coordinate changes on ideal-defined closed families and their polarized refinements. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {P Q : Over S}

/-- Transport an actual closed family by an isomorphism of ambient schemes. -/
def Closed.Families.FlatClosedFamily.changeAmbient (F : Closed.Families.FlatClosedFamily P) (e : P ≅ Q) : Closed.Families.FlatClosedFamily Q := by
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S).map e.inv))
  exact F.pullbackAlong e.inv.left (𝟙 S)
    (IsPullback.of_horiz_isIso ⟨e.inv.w.trans (Category.comp_id _).symm⟩)

theorem Closed.Families.FlatClosedFamily.changeAmbient_ideal (F : Closed.Families.FlatClosedFamily P) (e : P ≅ Q) :
    (F.changeAmbient e).ideal = F.ideal.comap e.inv.left := rfl

variable {g N : ℕ} {δ : Fin g → ℕ} {T U : Over S}

/-- Re-embedding through an ambient isomorphism is a Cartesian square. -/
theorem Embedded.PolarizedObjects.EmbeddedPolarizedObject.changeAmbient_isPullback
    (A : Embedded.PolarizedObjects.EmbeddedPolarizedObject P g δ N T) (e : P ≅ Q) :
    IsPullback (A.changeAmbient e).embedding.left (𝟙 A.object.abelian.scheme.left)
      (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).inv.left A.embedding.left := by
  have : IsIso (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).inv.left :=
    inferInstanceAs (IsIso ((Over.forget T.left).map (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).inv))
  change IsPullback (A.embedding.left ≫ (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).hom.left)
    (𝟙 A.object.abelian.scheme.left) (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).inv.left A.embedding.left
  apply IsPullback.of_vert_isIso
  constructor
  change (A.embedding.left ≫ (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).hom.left) ≫
    (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).inv.left = 𝟙 A.object.abelian.scheme.left ≫ A.embedding.left
  have he : (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).hom.left ≫ (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).inv.left =
      𝟙 (Embedded.FamilyFunctor.embeddedFamilyAmbient P T).left := congrArg Over.Hom.left (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).hom_inv_id
  rw [Category.assoc, he, Category.comp_id, Category.id_comp]

/-- The re-embedded ideal is the inverse-coordinate pullback of the original ideal. -/
theorem Embedded.PolarizedObjects.EmbeddedPolarizedObject.changeAmbient_ideal
    (A : Embedded.PolarizedObjects.EmbeddedPolarizedObject P g δ N T) (e : P ≅ Q) :
    (A.changeAmbient e).embedding.left.ker =
      A.embedding.left.ker.comap (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).inv.left := by
  let h := A.changeAmbient_isPullback e
  exact (congrArg Scheme.Hom.ker h.isoPullback_hom_fst).symm.trans
    ((Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom _).trans
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion A.embedding.left
        (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T).inv.left))

/-- Changing coordinates commutes with forgetting a polarized object to its closed family. -/
theorem Embedded.PolarizedObjects.EmbeddedPolarizedObject.changeAmbient_closedFamily
    (A : Embedded.PolarizedObjects.EmbeddedPolarizedObject P g δ N T) (e : P ≅ Q) :
    (A.changeAmbient e).closedFamily = A.closedFamily.changeAmbient (Embedded.AmbientIsomorphisms.embeddedAmbientIso e T) :=
  Closed.Families.FlatClosedFamily.ext (A.changeAmbient_ideal e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
