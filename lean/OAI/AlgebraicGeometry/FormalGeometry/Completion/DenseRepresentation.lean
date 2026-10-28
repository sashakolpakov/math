import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical

/-! # Dense Representation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.DenseRepresentation.Construction

noncomputable section

/-!
# Completion: extending a representative from a cover-dense full subcategory

The ordinary dense-subsite sheaf theorem extends a representing isomorphism
on the affine objects to the whole site.
-/

open _root_.CategoryTheory Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v' w

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) (ff : G.FullyFaithful)
  (J : GrothendieckTopology D) [J.Subcanonical] [G.IsCoverDense J]
  (F : Sheaf J (Type (max w v'))) {A : C}
  (rep : (G.op ⋙ F.obj).RepresentableBy A)

/-- The representing isomorphism on the image objects uses the actual full embedding. -/
def denseRepresentativeRestrictedIso :
    G.op ⋙ uliftYoneda.{w}.obj (G.obj A) ≅ G.op ⋙ F.obj :=
  NatIso.ofComponents
    (fun X => equivEquivIso (Equiv.ulift.trans (ff.homEquiv.symm.trans rep.homEquiv)))
    (by
      intro X Y g
      ext x
      change rep.homEquiv (ff.preimage (G.map g.unop ≫ x.down)) =
        F.obj.map (G.map g.unop).op (rep.homEquiv (ff.preimage x.down))
      rw [ff.preimage_comp, ff.preimage_map]
      exact rep.homEquiv_comp g.unop _)

/-- A sheaf represented on a full cover-dense subcategory is represented on the whole site. -/
def representableByOfCoverDense : F.obj.RepresentableBy (G.obj A) := by
  have := ff.full
  let Y : Sheaf J (Type (max w v')) :=
    ⟨uliftYoneda.{w}.obj (G.obj A), (isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)⟩
  let e : Y.obj ≅ F.obj :=
    Functor.IsCoverDense.Types.presheafIso (G := G)
      (denseRepresentativeRestrictedIso G ff J F rep)
  exact (Functor.RepresentableBy.equivUliftYonedaIso F.obj (G.obj A)).symm e

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.DenseRepresentation.Construction
