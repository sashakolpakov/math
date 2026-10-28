import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.Units
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Frame Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.FrameCover

noncomputable section

/-! A finite affine frame cover of an actual line bundle on a qcqs
inverse limit is the pullback of an affine cover at a finite stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
theorem exists_limit_line_frame_cover_stage (L : HilbertConstruction.Line.Bundles.LineBundle c.pt) :
    ∃ (i : I) (n : ℕ) (V : Fin n → (D.obj i).Opens),
      IsOpenCover V ∧ (∀ j, IsAffineOpen (V j)) ∧
      (∀ j, Nonempty ((Scheme.Modules.pullback (c.π.app i ⁻¹ᵁ V j).ι).obj L.sheaf ≅
        HilbertConstruction.Line.Bundles.structureModule (c.π.app i ⁻¹ᵁ V j).toScheme)) := by
  let : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨n, U, hU, hframe, hcover⟩ := L.exists_finite_affine_frames
  have hUcover : IsOpenCover U := by
    apply top_unique
    intro x _
    obtain ⟨j, hj⟩ := hcover x
    exact Opens.mem_iSup.mpr ⟨j, hj⟩
  obtain ⟨i, V, hV, hVU⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite D c hc U hUcover hU
  refine ⟨i, n, V, hV, fun j => (hVU j).1, ?_⟩
  intro j
  rw [← (hVU j).2]
  exact hframe j

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.FrameCover
