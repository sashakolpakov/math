import OAI.AlgebraicGeometry.Resolution.Blowups.CenterGeneratorReplacement
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoordinateCenterChart

/-! # Replaced Center Coordinate Indices -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ReplacedCenterCoordinateIndices.Construction

noncomputable section

/-! Exact coordinate indices for a center after replacing one generator. -/

universe u

def centerReplacementCoordinateEmbedding {σ : Type u} (C : Finset σ) (i : C) :
    Option {j : C // i ≠ j} ↪ Option {j : σ // i.val ≠ j} :=
  Function.Embedding.optionMap
    ⟨fun j => ⟨j.val.val, fun h => j.property (Subtype.ext h)⟩,
      by
        intro a b h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : {j : σ // i.val ≠ j} => x.val) h⟩

theorem replaced_center_coordinate_ideal
    {σ k R : Type u} [DecidableEq σ] [Fintype σ] [CommRing k] [CommRing R]
    (C : Finset σ) (i : C) (g : σ → R) (z : R)
    (φ : MvPolynomial (Option {j : σ // i.val ≠ j}) k →+* R)
    (hzero : φ (MvPolynomial.X none) = z)
    (hrest : ∀ j : {j : σ // i.val ≠ j}, φ (MvPolynomial.X (some j)) = g j.val) :
    (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (Finset.univ.image (centerReplacementCoordinateEmbedding C i))).map φ =
      Ideal.span (Set.range (CenterGeneratorReplacement.Construction.centerReplacementFamily (fun j : C => g j.val) i z)) := by
  rw [Boundary.CoordinateCenterChart.Construction.subsetCoordinateIdeal_map_embedded_family (centerReplacementCoordinateEmbedding C i) φ]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  cases j with
  | none => exact hzero
  | some j => exact hrest ⟨j.val.val, fun h => j.property (Subtype.ext h)⟩

theorem centerReplacementCoordinateEmbedding_mem_iff
    {σ : Type u} [Fintype σ] [DecidableEq σ] (C : Finset σ) (i : C)
    (s : {j : σ // i.val ≠ j}) :
    some s ∈ Finset.univ.image (centerReplacementCoordinateEmbedding C i) ↔ s.val ∈ C := by
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    cases j with
    | none => cases hj
    | some j =>
        have he : j.val.val = s.val := congrArg Subtype.val (Option.some.inj hj)
        exact he ▸ j.val.property
  · intro hs
    let j : {j : C // i ≠ j} := ⟨⟨s.val, hs⟩, fun h => s.property (congrArg Subtype.val h)⟩
    exact Finset.mem_image.mpr ⟨some j, Finset.mem_univ _, rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ReplacedCenterCoordinateIndices.Construction
