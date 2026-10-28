import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.ModelRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.NamedActiveContainedCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterRestoreInactiveLabels
import OAI.AlgebraicGeometry.Resolution.Blowups.UnitBoundaryPrincipalNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.MixedBoundaryFamily

/-! # Contained Hypersurface Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A contained transverse hypersurface is compatible with the full modeled center and boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.contained_hypersurface_center_chart
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {w : ι → R}
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (C : Finset M.indices) (F : Finset ι)
    (hF : ∀ j, j ∈ F ↔ ∃ s ∈ C, M.coordinate j = some s)
    (p : PrimeSpectrum R) (hC : (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map ≤ p.asIdeal)
    (z : R) (hz : z ∈ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map)
    (E : Derivation k R R) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (hEz : E z ∉ p.asIdeal) :
    Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map)
      (fun j : Option ι => match j with | none => z | some j => w j)
      (insert none (F.image some)) p) := by
  classical
  let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map
  let B : Finset ι := Finset.univ.filter (fun j => w j ∈ p.asIdeal)
  have hB (j : ι) : j ∈ B ↔ w j ∈ p.asIdeal := by simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
  have hFB : F ⊆ B := by
    intro j hj
    exact (hB j).mpr (hC (M.coordinateCenter_boundary_mem C F hF j hj))
  obtain ⟨f, hf, hu⟩ := UnitBoundaryPrincipalNeighborhood.Construction.exists_unit_boundary_principal_neighborhood
    (fun j : {j : ι // j ∉ B} => w j.val) p (fun j => by
      intro h
      exact j.property ((hB j.val).mpr h))
  let A := Localization.Away f
  let γ : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  let : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway f
  have hγ : γ.toRingHom.Etale := RingHom.etale_algebraMap.mpr inferInstance
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom γ.toRingHom)) := IsOpenImmersion.of_isLocalization f
  obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime f p hf
  have hQI : Q.asIdeal.comap (algebraMap R A) = p.asIdeal := congrArg PrimeSpectrum.asIdeal hQ
  let eB : B ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  let N := (M.reindex eB).baseChange γ hγ
  let G := ActiveBoundaryLabelRestriction.Construction.restrictedBoundaryDividedLabels B F
  have hG (j : B) : j ∈ G ↔ ∃ s ∈ C, N.coordinate j = some s := by
    change j ∈ ActiveBoundaryLabelRestriction.Construction.restrictedBoundaryDividedLabels B F ↔ ∃ s ∈ C, M.coordinate j.val = some s
    simp only [ActiveBoundaryLabelRestriction.Construction.restrictedBoundaryDividedLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hF j.val
  have hmap : I.map γ.toRingHom = (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map N.map := by
    change ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map).map γ.toRingHom =
      (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (γ.toRingHom.comp M.map)
    rw [Ideal.map_map]
  have hcenter : I.map γ.toRingHom ≤ Q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    change I ≤ Q.asIdeal.comap (algebraMap R A)
    rw [hQI]
    exact hC
  have hwA (j : B) : γ (w j.val) ∈ Q.asIdeal := by
    change w j.val ∈ Q.asIdeal.comap (algebraMap R A)
    rw [hQI]
    exact (hB j.val).mp j.property
  let D := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) E
  have hD : D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun j : B => γ (w j.val)) := by
    have h := Relative.LogarithmicBoundary.Construction.extendEtaleRingDerivation_relative_logarithmic (S := A) k w ⟨E, hE⟩
    intro j
    exact h j.val
  have hDz : D (γ z) ∉ Q.asIdeal := by
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) E (algebraMap R A z) ∉ Q.asIdeal
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap]
    intro h
    apply hEz
    have h' : E z ∈ Q.asIdeal.comap (algebraMap R A) := h
    rwa [hQI] at h'
  have hzA : γ z ∈ I.map γ.toRingHom := Ideal.mem_map_of_mem γ.toRingHom hz
  have hlocal := Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel.named_active_contained_hypersurface_center_chart (R := .of A)
    N (I.map γ.toRingHom) C hmap G hG Q hcenter hwA (γ z) hzA D hD hDz
  obtain ⟨O⟩ := hlocal
  dsimp only [eB, G] at O
  simp only [Function.Embedding.coeFn_mk] at O
  let O' := MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.restoreInactiveWithNormal
    (k := k) (R := .of A) (I := I.map γ.toRingHom) (p := Q)
    B F hFB (γ z) (fun j => γ (w j)) (fun j hj => hu ⟨j, hj⟩) (by
      convert O using 1
      funext j
      cases j <;> rfl)
  let v : Option ι → R := fun j => match j with | none => z | some j => w j
  have heq : (fun j : Option ι => match j with | none => γ z | some j => γ (w j)) =
      (fun j => γ (v j)) := by
    funext j
    cases j <;> rfl
  have O'' : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k (.of A) (I.map γ.toRingHom)
      (fun j => γ (v j)) (insert none (F.image some)) Q := by
    convert O' using 1
    exact heq.symm
  exact ⟨MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.comp (R := R) (S := .of A)
    I v (insert none (F.image some)) γ O'' p hQ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
