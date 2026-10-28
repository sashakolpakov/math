import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ModelProjectiveEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.EmbeddingIso

/-! # Prescribed Closed Family Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The prescribed ideal-defined family is smooth and preserves the model's projective embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {C K R : CommRingCat.{u}} (φ : C ⟶ K) (r : Spec R ⟶ Spec K)
variable {X : Over (Spec C)} {n : ℕ} (i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace C n) [IsClosedImmersion i.left]
variable (L : HilbertConstruction.Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel ((Over.pullback (Spec.map φ)).obj X) r)

theorem Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedClosedFamilyIso_inclusion :
    (L.prescribedClosedFamilyIso φ r i).hom ≫ (L.prescribedClosedFamily φ r i).inclusion =
      L.prescribedEmbedding φ r i := by
  have : Smooth L.scheme.hom := L.smooth
  have : IsClosedImmersion (L.prescribedEmbedding φ r i).left := L.prescribedEmbedding_closed φ r i
  exact Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion (L.prescribedEmbedding φ r i)

theorem Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedClosedFamily_smooth : Smooth (L.prescribedClosedFamily φ r i).scheme.hom := by
  let e := L.prescribedClosedFamilyIso φ r i
  have : Smooth L.scheme.hom := L.smooth
  have : IsIso e.inv.left := (Over.forget (Spec K)).map_isIso e.inv
  have hs : Smooth (e.inv.left ≫ L.scheme.hom) := inferInstance
  exact (congrArg Smooth e.inv.w).mp hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
