import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Dimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.CoverDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.AffinePullback

/-! # Scheme Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.SchemeDimension.Construction

noncomputable section

/-! The dimension bound is retained by arbitrary actual étale morphisms of schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem scheme_dimension_le_of_etale {X Y : Scheme.{0}} (q : Y ⟶ X) [Etale q]
    (d : WithBot ℕ∞) (hd : topologicalKrullDim X ≤ d) : topologicalKrullDim Y ≤ d := by
  choose U V hsub hmem using IdealSheaf.ProductPullback.Construction.exists_affine_pair_at_point q
  have hcover : ⨆ y : Y, (V y).1 = ⊤ := by
    apply top_le_iff.mp
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hmem y⟩
  let C := Global.MonomialBoundaryAtlas.Construction.chosenAffineSpecCover V hcover
  apply Open.CoverDimension.Construction.scheme_dimension_le_of_open_affine_cover C.X C.f (fun y => ⟨C.idx y, C.covers y⟩) d
  intro y
  let : IsOpenImmersion (U y).2.fromSpec := (U y).2.isOpenImmersion_fromSpec
  exact (Dimension.Construction.ringKrullDim_le_of_etale (q.appLE (U y).1 (V y).1 (hsub y)).hom
    (q.etale_appLE (U y).2 (V y).2 (hsub y))).trans
      ((Open.CoverDimension.Construction.ringKrullDim_le_of_affine_open_map Γ(X, U y) (U y).2.fromSpec).trans hd)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.SchemeDimension.Construction
