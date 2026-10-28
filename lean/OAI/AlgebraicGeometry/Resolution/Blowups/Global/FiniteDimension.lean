import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.TypeRingDimensionBound
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.CoverDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas

/-! # Finite Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.FiniteDimension.Construction

noncomputable section

/-! Compact smooth complex schemes have a finite global dimension bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_global_complex_dimension_bound
    {X : Scheme} [CompactSpace X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] :
    ∃ d : ℕ, topologicalKrullDim X ≤ d := by
  classical
  have hex (U : X.affineOpens) : ∃ d : ℕ, ringKrullDim Γ(X, U) ≤ d := by
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
    exact Finite.TypeRingDimensionBound.Construction.finiteType_ringKrullDim_bounded ℂ Γ(X, U)
  choose d hd using hex
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := Set.univ)).mp
      ⟨isCompact_univ, isOpen_univ⟩
  let N := hs.toFinset.sup d
  let U (i : hs.toFinset) : X.affineOpens := i.val
  have hU : ⨆ i, (U i).1 = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have hx : x ∈ ⋃ V ∈ s, (V : Set X) := hcover ▸ Set.mem_univ x
    obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp hx
    exact Opens.mem_iSup.mpr ⟨⟨V, hs.mem_toFinset.mpr hV⟩, hxV⟩
  let C := MonomialBoundaryAtlas.Construction.chosenAffineSpecCover U hU
  let : ∀ i, IsOpenImmersion (C.f i) := fun i => C.openCover.map_prop i
  refine ⟨N, Open.CoverDimension.Construction.scheme_dimension_le_of_open_affine_cover C.X C.f
    (fun x => ⟨C.idx x, C.covers x⟩) N ?_⟩
  intro i
  exact (hd i.val).trans (Nat.cast_le.mpr (Finset.le_sup i.property))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.FiniteDimension.Construction
