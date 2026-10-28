import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport

/-! # Local Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Equality of embedded closed families can be checked on an affine cover of the ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X S : Scheme.{u}}

/-- Ideal sheaves agree if their pullbacks agree on an affine spectrum cover. -/
theorem ClosedFamily.LocalEquality.ideal_eq_of_affine_cover (C : Scheme.AffineOpenCover.{v} X)
    (I J : X.IdealSheafData) (h : ∀ i, I.comap (C.f i) = J.comap (C.f i)) : I = J := by
  let U (i : C.I₀) : X.affineOpens :=
    ⟨C.f i ''ᵁ ⊤, (isAffineOpen_top (Spec (C.X i))).image_of_isOpenImmersion (C.f i)⟩
  have hU : (⨆ i, (U i).1) = ⊤ := by
    have hC : (⨆ i, (C.f i).opensRange) = ⊤ := C.openCover.iSup_opensRange
    simpa only [U, Scheme.Hom.image_top_eq_opensRange] using hC
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hU
  intro i
  have hi := congrArg (fun K : (Spec (C.X i)).IdealSheafData =>
    K.ideal ⟨⊤, isAffineOpen_top (Spec (C.X i))⟩) (h i)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hi
  exact Ideal.comap_injective_of_surjective ((C.f i).appIso ⊤).inv.hom
    (ConcreteCategory.bijective_of_isIso ((C.f i).appIso ⊤).inv).2 hi

/-- An embedded flat family is determined by the restrictions of its defining ideal to an affine cover. -/
theorem Closed.Families.FlatClosedFamily.ext_on_affine_cover {P : Over S} (F G : Closed.Families.FlatClosedFamily P)
    (C : Scheme.AffineOpenCover.{v} P.left)
    (h : ∀ i, F.ideal.comap (C.f i) = G.ideal.comap (C.f i)) : F = G :=
  Closed.Families.FlatClosedFamily.ext (ClosedFamily.LocalEquality.ideal_eq_of_affine_cover C F.ideal G.ideal h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
