import OAI.AlgebraicGeometry.Resolution.Blowups.TransverseContainedCenterCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.ReplacementBoundaryEmbedding
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.AdjoinCoordinate
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.EquationCongruence
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.Coordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts

/-! # Contained Hypersurface Center Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Adjoin a contained transverse hypersurface to common center and active boundary coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

/-- At a center point where the displayed old boundary is active, a
transverse contained equation can be adjoined to the boundary without
changing the actual center. All divided-label conditions remain exact. -/
theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.active_contained_hypersurface_center_chart
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} [DecidableEq ι] {w : ι → R} (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (C : Finset M.indices) (F : Finset ι)
    (hF : ∀ j, j ∈ F ↔ ∃ s ∈ C, M.coordinate j = some s)
    (p : PrimeSpectrum R) (hC : (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map ≤ p.asIdeal)
    (hw : ∀ j, w j ∈ p.asIdeal) (z : R) (hz : z ∈ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map)
    (E : Derivation k R R) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (hEz : E z ∉ p.asIdeal) :
    Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map)
      (fun j : Option ι => match j with | none => z | some j => w j)
      (insert none (F.image some)) p) := by
  classical
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  let : IsScalarTower k (MvPolynomial M.indices k) R :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
  have hB (s : M.indices) (hs : s ∈ M.boundaryIndices) : M.map (MvPolynomial.X s) ∈ p.asIdeal := by
    obtain ⟨j, hj⟩ := (M.mem_boundaryIndices s).mp hs
    apply (p.asIdeal.unit_mul_mem_iff_mem (M.multiplierUnit j)).mp
    simpa only [M.equation j, hj] using hw j
  have hEB (s : M.indices) (hs : s ∈ M.boundaryIndices) :
      E (M.map (MvPolynomial.X s)) ∈ Ideal.span {M.map (MvPolynomial.X s)} := by
    rw [M.logarithmic_coordinates] at hE
    exact hE ⟨s, hs⟩
  obtain ⟨f, i, hf, hiB, φ, hφ, hzero, hrest, hcenter⟩ :=
    TransverseContainedCenterCoordinates.Construction.exists_transverse_contained_center_coordinates C M.boundaryIndices p.asIdeal hC hB z hz E hEB hEz
  let A := Localization.Away f
  let γ : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  let e := ReplacementBoundaryEmbedding.Construction.replacementBoundaryEmbedding M.boundaryIndices i.val hiB
  have he (s : M.boundaryIndices) : φ (MvPolynomial.X (e s)) = γ (M.map (MvPolynomial.X s.val)) :=
    hrest ⟨s.val, fun h => hiB (h.symm ▸ s.property)⟩
  have hground (c : k) : φ (MvPolynomial.C c) = algebraMap k A c := φ.commutes c
  let N := M.replaceCoordinates γ φ.toRingHom hφ hground e he
  have hnone (j : ι) : N.coordinate j ≠ some none :=
    M.replaceCoordinates_unused γ φ.toRingHom hφ hground e he none
      (ReplacementBoundaryEmbedding.Construction.replacementBoundaryEmbedding_ne_none M.boundaryIndices i.val hiB) j
  let v : Option ι → R := fun j => match j with | none => z | some j => w j
  let N' := (N.adjoinEquation (γ z) none hnone hzero).congrEquations (fun j => γ (v j))
    (by intro j; cases j <;> rfl)
  obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime f p hf
  let O : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R v p :=
    { carrier := .of A
      algebra := inferInstance
      map := γ
      isOpenImmersion := IsOpenImmersion.of_isLocalization f
      point := Q
      point_over := hQ
      model := N' }
  let K := Finset.univ.image (ReplacedCenterCoordinateIndices.Construction.centerReplacementCoordinateEmbedding C i)
  refine ⟨{ chart := O
            coordinates := K
            center_eq := hcenter
            divided_iff := ?_ }⟩
  intro j
  cases j with
  | none =>
      change none ∈ insert none (F.image some) ↔ ∃ s ∈ K, some none = some s
      constructor
      · intro _
        exact ⟨none, Finset.mem_image.mpr ⟨none, Finset.mem_univ _, rfl⟩, rfl⟩
      · intro _
        exact Finset.mem_insert_self _ _
  | some j =>
      change some j ∈ insert none (F.image some) ↔
        ∃ s ∈ K, (M.boundaryCoordinate j).map e = some s
      have hmem : some j ∈ insert none (F.image some) ↔ j ∈ F := by simp
      rw [hmem, hF j]
      have h := ReplacementBoundaryEmbedding.Construction.replacement_boundary_center_iff C M.boundaryIndices i hiB (M.boundaryCoordinate j)
      rw [M.boundaryCoordinate_map] at h
      exact h.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
