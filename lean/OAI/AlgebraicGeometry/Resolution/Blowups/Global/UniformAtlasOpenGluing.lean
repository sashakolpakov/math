import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedAtlasOpenGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.RefinementAtlas

/-! # Uniform Atlas Open Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.UniformAtlasOpenGluing.Construction

noncomputable section

/-! Fixed incidence sets and full boundary atlases glue on an actual open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_uniform_mixed_atlas_of_openCover
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData) (F : Finset β) (C : Scheme.OpenCover.{0, 0} X)
    (h : ∀ i, ∃ A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (C.f i ≫ f) (I.comap (C.f i))
      (fun l => (D l).comap (C.f i)), ∀ a, A.divided a = F) :
    ∃ A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D, ∀ a, A.divided a = F := by
  classical
  choose A hA using h
  refine ⟨CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofOpenCover f I D C A, ?_⟩
  intro a
  change (Σ i : C.I₀, (A i).indices) at a
  exact hA a.1 a.2

theorem exists_boundary_atlas_of_openCover
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (C : Scheme.OpenCover.{0, 0} X)
    (h : ∀ i, Nonempty (MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (C.f i ≫ f)
      (fun l => (D l).comap (C.f i)) [Finset.univ])) :
    Nonempty (MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) := by
  classical
  let A := fun i => (h i).some
  have hu : ∀ i, CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (C.f i ≫ f) ((⊤ : X.IdealSheafData).comap (C.f i))
      (fun l => (D l).comap (C.f i)) := by
    intro i
    rw [Scheme.IdealSheafData.comap_top]
    exact (A i).unitCenter
  exact ⟨(CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofOpenCover f ⊤ D C hu).boundaryAtlas⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.UniformAtlasOpenGluing.Construction
