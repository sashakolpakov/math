import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PolarizedObjects

/-! # Polarized Family Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded

noncomputable section

/-! Forgetting an embedded polarized object to its ideal-sheaf family commutes with base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {P : Over S} {g N : ℕ} {δ : Fin g → ℕ} {T U : Over S}

theorem PolarizedFamilyMap.embeddedFamilyAmbientBaseChangeIso_hom_map (f : T ⟶ U) :
    (PolarizedObjects.embeddedFamilyAmbientBaseChangeIso P f).hom.left ≫ FamilyFunctor.embeddedFamilyAmbientMap P f =
      pullback.fst (FamilyFunctor.embeddedFamilyAmbient P U).hom f.left :=
  (FamilyFunctor.embeddedFamilyAmbient_isPullback P f).isoPullback_inv_fst

/-- The new embedding and the ambient base-change map form a Cartesian square. -/
theorem PolarizedObjects.EmbeddedPolarizedObject.pullback_embedding_isPullback (A : PolarizedObjects.EmbeddedPolarizedObject P g δ N U) (f : T ⟶ U) :
    IsPullback (A.pullback f).embedding.left (pullback.fst A.object.abelian.scheme.hom f.left)
      (FamilyFunctor.embeddedFamilyAmbientMap P f) A.embedding.left := by
  let q := pullback.fst A.object.abelian.scheme.hom f.left
  let i := (A.pullback f).embedding.left
  have hc : i ≫ FamilyFunctor.embeddedFamilyAmbientMap P f = q ≫ A.embedding.left := by
    change (((Over.pullback f.left).map A.embedding).left ≫
      (PolarizedObjects.embeddedFamilyAmbientBaseChangeIso P f).hom.left) ≫ FamilyFunctor.embeddedFamilyAmbientMap P f = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun p => ((Over.pullback f.left).map A.embedding).left ≫ p)
        (PolarizedFamilyMap.embeddedFamilyAmbientBaseChangeIso_hom_map f)).trans (pullback.lift_fst _ _ _))
  have hi : i ≫ (FamilyFunctor.embeddedFamilyAmbient P T).hom =
      pullback.snd A.object.abelian.scheme.hom f.left := (A.pullback f).embedding.w
  have hb : A.embedding.left ≫ (FamilyFunctor.embeddedFamilyAmbient P U).hom = A.object.abelian.scheme.hom :=
    A.embedding.w
  have hr : IsPullback (i ≫ (FamilyFunctor.embeddedFamilyAmbient P T).hom) q f.left
      (A.embedding.left ≫ (FamilyFunctor.embeddedFamilyAmbient P U).hom) :=
    (congrArg₂ (fun a b => IsPullback a q f.left b) hi hb).mpr
      (IsPullback.of_hasPullback A.object.abelian.scheme.hom f.left).flip
  exact IsPullback.of_right hr hc (FamilyFunctor.embeddedFamilyAmbient_isPullback P f).flip

/-- The defining ideal of the pulled-back embedding is the pullback of its original ideal. -/
theorem PolarizedObjects.EmbeddedPolarizedObject.pullback_embedding_ideal (A : PolarizedObjects.EmbeddedPolarizedObject P g δ N U) (f : T ⟶ U) :
    (A.pullback f).embedding.left.ker = A.embedding.left.ker.comap (FamilyFunctor.embeddedFamilyAmbientMap P f) := by
  let h := A.pullback_embedding_isPullback f
  exact (congrArg Scheme.Hom.ker h.isoPullback_hom_fst).symm.trans
    ((Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom _).trans
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion A.embedding.left (FamilyFunctor.embeddedFamilyAmbientMap P f)))

/-- Forgetting polarization and level to the embedded flat family respects base change. -/
theorem PolarizedObjects.EmbeddedPolarizedObject.closedFamily_pullback (A : PolarizedObjects.EmbeddedPolarizedObject P g δ N U) (f : T ⟶ U) :
    (A.pullback f).closedFamily = (FamilyFunctor.embeddedFlatFamilyFunctor P).map f.op A.closedFamily :=
  Closed.Families.FlatClosedFamily.ext (A.pullback_embedding_ideal f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded
