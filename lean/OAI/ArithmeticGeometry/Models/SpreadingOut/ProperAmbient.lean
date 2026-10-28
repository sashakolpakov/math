import OAI.ArithmeticGeometry.Models.SpreadingOut.SchematicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Proper Ambient -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.ProperAmbient.Construction

noncomputable section

/-! Proper models obtained by schematic closure in a proper ambient scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- Closing a subscheme of the generic fiber of a proper ambient scheme
produces a proper model with exactly that generic fiber. -/
theorem closed_generic_subscheme_has_proper_model
    {S T : Scheme.{u}} (g : T ⟶ S) [IsPreimmersion g] [QuasiCompact g]
    (P : Over S) [IsProper P.hom]
    (X : Over T) (i : X ⟶ (Over.pullback g).obj P)
    [IsClosedImmersion i.left] :
    ∃ M : Over S, IsProper M.hom ∧
      Nonempty ((Over.pullback g).obj M ≅ X) := by
  let j := pullback.fst P.hom g
  let f := i.left ≫ j
  let M : Over S := Over.mk (f.imageι ≫ P.hom)
  have hp : IsProper M.hom := by
    dsimp [M]
    infer_instance
  have h : IsPullback f.toImage X.hom M.hom g := by
    have hc := (SchematicClosure.Construction.schematicClosure_isPullback i.left j).flip
    have ht := hc.paste_vert (IsPullback.of_hasPullback P.hom g)
    have hi : i.left ≫ pullback.snd P.hom g = X.hom := i.w
    rw [hi] at ht
    exact ht
  exact ⟨M, hp, ⟨Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd⟩⟩

theorem proper_schematic_image
    {S : Scheme.{u}} (X Y : Over S)
    [IsProper X.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) : IsProper (f.left.imageι ≫ Y.hom) := by
  have : IsProper (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : IsProper f.left := IsProper.of_comp f.left Y.hom
  have : Surjective f.left.toImage := inferInstance
  have : UniversallyClosed (f.left.toImage ≫ (f.left.imageι ≫ Y.hom)) := by
    rw [← Category.assoc, f.left.toImage_imageι, f.w]
    infer_instance
  have : UniversallyClosed (f.left.imageι ≫ Y.hom) :=
    UniversallyClosed.of_comp_surjective f.left.toImage _
  exact ⟨⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.ProperAmbient.Construction
