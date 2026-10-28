import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdealDescent

/-! # Ideal Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Effective gluing of compatible ideal sheaves on a locally directed open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {C : X.OpenCover} [Category C.I₀] [C.LocallyDirected]
variable [Small.{u} C.I₀] [Quiver.IsThin C.I₀] (D : IdealDescent.IdealDescentData C)

/-- The glued local closed subschemes give a closed immersion into the ambient scheme. -/
theorem IdealDescent.IdealDescentData.glued_closedImmersion : IsClosedImmersion D.relativeGluingData.toBase := by
  apply IsZariskiLocalAtTarget.of_openCover C
  intro i
  let h := (D.relativeGluingData.isPullback_natTrans_ι_toBase i).flip
  have he : C.pullbackHom D.relativeGluingData.toBase i =
      h.isoPullback.inv ≫ (D.ideal i).subschemeι := h.isoPullback_inv_snd.symm
  rw [he]
  exact @IsClosedImmersion.comp _ _ _ h.isoPullback.inv (D.ideal i).subschemeι
    inferInstance (inferInstanceAs (IsClosedImmersion (D.ideal i).subschemeι))

/-- The actual defining ideal of the glued closed subscheme. -/
def IdealDescent.IdealDescentData.gluedIdeal : X.IdealSheafData := D.relativeGluingData.toBase.ker

/-- The glued ideal restricts to precisely the prescribed local ideal on each chart. -/
theorem IdealDescent.IdealDescentData.gluedIdeal_comap (i : C.I₀) : (D.gluedIdeal).comap (C.f i) = D.ideal i := by
  have : IsClosedImmersion D.relativeGluingData.toBase := D.glued_closedImmersion
  let h := D.relativeGluingData.isPullback_natTrans_ι_toBase i
  have he : (D.ideal i).subschemeι.ker = D.gluedIdeal.comap (C.f i) :=
    (congrArg Scheme.Hom.ker h.isoPullback_hom_fst).symm.trans
      ((Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom _).trans
        (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion D.relativeGluingData.toBase (C.f i)))
  exact he.symm.trans (D.ideal i).ker_subschemeι

/-- Compatible local ideals glue to a unique global quasi-coherent ideal sheaf. -/
theorem IdealDescent.IdealDescentData.existsUnique_ideal : ∃! I : X.IdealSheafData, ∀ i, I.comap (C.f i) = D.ideal i := by
  refine ⟨D.gluedIdeal, D.gluedIdeal_comap, ?_⟩
  intro I hI
  exact ClosedFamily.OpenEquality.ideal_eq_of_open_cover C I D.gluedIdeal
    (fun i => (hI i).trans (D.gluedIdeal_comap i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
