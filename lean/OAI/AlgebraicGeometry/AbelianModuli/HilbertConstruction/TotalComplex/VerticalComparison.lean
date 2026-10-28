import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.HomologyComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.VerticalEdge

/-! # Vertical Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.VerticalComparison

noncomputable section

/-! The positive-degree column comparison, obtained by flipping the actual double complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)]

/-- Exact augmented columns give the vertical edge comparison in every positive degree. -/
theorem vertical_edge_quasiIsoAt
    (B : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ p, B.X p ⟶ (K.X 0).X p)
    (he : ∀ p p', (ComplexShape.up ℕ).Rel p p' →
      e p ≫ (K.X 0).d p p' = B.d p p' ≫ e p')
    (w : ∀ p, e p ≫ (K.d 0 1).f p = 0)
    (haug : ∀ p, (ShortComplex.mk (e p) ((K.d 0 1).f p) (w p)).Exact)
    (hmono : ∀ p, Mono (e p)) (hcols : CycleNormalization.RowsExact K.flip) (n : ℕ) :
    QuasiIsoAt (VerticalEdge.totalUpNatVerticalEdge K B e he w) (n + 1) := by
  let edge := HorizontalEdge.totalUpNatHorizontalEdge K.flip B e he w
  have : QuasiIsoAt edge (n + 1) :=
    HomologyComparison.horizontal_edge_quasiIsoAt K.flip B e he w haug hmono hcols n
  have : QuasiIsoAt (K.totalFlipIso (.up ℕ)).hom (n + 1) :=
    quasiIsoAt_of_isIso _ _
  change QuasiIsoAt (edge ≫ (K.totalFlipIso (.up ℕ)).hom) (n + 1)
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.VerticalComparison
