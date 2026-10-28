import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyDescentData

/-! # Family Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyGluing.EmbeddedFamilyDescentData

noncomputable section

/-! Effective descent of embedded flat families along a locally directed open cover of the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {P T : Over S} {C : T.left.OpenCover}
variable [Category C.I₀] [C.LocallyDirected] [Small.{u} C.I₀] [Quiver.IsThin C.I₀]
variable (D : FamilyDescentData.EmbeddedFamilyDescentData P T C)

local instance : Small.{u} (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom).I₀ :=
  inferInstanceAs (Small.{u} C.I₀)

local instance : Quiver.IsThin (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom).I₀ :=
  inferInstanceAs (Quiver.IsThin C.I₀)

/-- The global embedded flat family obtained from the compatible local families. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyDescentData.EmbeddedFamilyDescentData.glue : Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P T) :=
  Closed.Families.FlatClosedFamily.glue D.idealDescentData D.canonicalFamily_flat D.canonicalFamily_locallyFinitePresentation

/-- The glued ideal pulls back to the exact original ideal over each member of the base cover. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyDescentData.EmbeddedFamilyDescentData.glue_ideal_pullback (i : C.I₀) :
    D.glue.ideal.comap (FamilyFunctor.embeddedFamilyAmbientMap P (FamilyOpenCover.overOpenCoverMap T C i)) = (D.family i).ideal := by
  let e := CoverComparisons.embeddedCoverIso P T C i
  let b := (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom).f i
  let c := FamilyFunctor.embeddedFamilyAmbientMap P (FamilyOpenCover.overOpenCoverMap T C i)
  have hi : D.glue.ideal.comap b = (D.family i).ideal.comap e.inv.left :=
    Closed.Families.FlatClosedFamily.glue_ideal_comap D.idealDescentData D.canonicalFamily_flat
      D.canonicalFamily_locallyFinitePresentation i
  have he : e.hom.left ≫ b = c :=
    (FamilyFunctor.embeddedFamilyAmbient_isPullback P (FamilyOpenCover.overOpenCoverMap T C i)).isoPullback_hom_fst
  have hee : e.hom.left ≫ e.inv.left =
      𝟙 (FamilyFunctor.embeddedFamilyAmbient P (FamilyOpenCover.overOpenCoverObject T C i)).left :=
    congrArg Over.Hom.left e.hom_inv_id
  change D.glue.ideal.comap c = (D.family i).ideal
  exact (congrArg (fun a => D.glue.ideal.comap a) he.symm).trans
    ((D.glue.ideal.comap_comp e.hom.left b).trans
      ((congrArg (fun I => I.comap e.hom.left) hi).trans
        (((D.family i).ideal.comap_comp e.hom.left e.inv.left).symm.trans
          ((congrArg (fun a => (D.family i).ideal.comap a) hee).trans
            (D.family i).ideal.comap_id))))

/-- The global family's restrictions are the prescribed local flat families. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyDescentData.EmbeddedFamilyDescentData.glue_pullback (i : C.I₀) :
    (FamilyFunctor.embeddedFlatFamilyFunctor P).map (FamilyOpenCover.overOpenCoverMap T C i).op D.glue = D.family i :=
  Closed.Families.FlatClosedFamily.ext (D.glue_ideal_pullback i)

/-- Compatible embedded flat families on a directed base cover glue uniquely. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyDescentData.EmbeddedFamilyDescentData.existsUnique_glue : ∃! F : Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P T),
    ∀ i, (FamilyFunctor.embeddedFlatFamilyFunctor P).map (FamilyOpenCover.overOpenCoverMap T C i).op F = D.family i := by
  refine ⟨D.glue, D.glue_pullback, ?_⟩
  intro F hF
  exact FamilyOpenCover.embeddedFlatFamily_eq_of_open_cover C F D.glue
    (fun i => (hF i).trans (D.glue_pullback i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyGluing.EmbeddedFamilyDescentData
