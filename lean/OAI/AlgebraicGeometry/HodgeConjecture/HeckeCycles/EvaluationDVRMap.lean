import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVRLifts
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-! # Evaluation DVR Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationDVRMap.CM

noncomputable section

/-! Field embeddings between finite evaluation fields extend to their
actual DVRs of integers. The original residue identifications force
compatibility with the same residue field. -/

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVRLifts

variable {R K L L' : Type} [CommRing R] [IsLocalRing R]
  [Field K] [Algebra R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Field L'] [Algebra K L'] [Algebra R L'] [IsScalarTower R K L']
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR R L) (V' : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR R L') (σ : L →ₐ[K] L')

def map : V.carrier →ₐ[R] V'.carrier := galRestrict' R V.carrier V'.carrier σ

theorem map_fraction (x : V.carrier) :
    algebraMap V'.carrier L' (CM.map V V' σ x) = σ (algebraMap V.carrier L x) :=
  algebraMap_galRestrict'_apply R V.carrier V'.carrier σ x

theorem map_injective : Function.Injective (CM.map V V' σ) := by
  intro x y h
  apply IsFractionRing.injective V.carrier L
  apply σ.injective
  exact (map_fraction V V' σ x).symm.trans
    ((congrArg (algebraMap V'.carrier L') h).trans (map_fraction V V' σ y))

instance map_local : IsLocalHom (CM.map V V' σ).toRingHom := by
  have he : (CM.map V V' σ).toRingHom.comp (algebraMap R V.carrier) = algebraMap R V'.carrier :=
    RingHom.ext (CM.map V V' σ).commutes
  have h : ((CM.map V V' σ).toRingHom.comp (algebraMap R V.carrier)).IsIntegral := by
    rw [he]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  exact (RingHom.IsIntegral.tower_top (algebraMap R V.carrier) (CM.map V V' σ).toRingHom h).isLocalHom
    (map_injective V V' σ)

theorem residue_map (x : IsLocalRing.ResidueField R) :
    IsLocalRing.ResidueField.map (CM.map V V' σ).toRingHom (V.residueIso x) = V'.residueIso x := by
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  rw [V.residue_compatible, IsLocalRing.ResidueField.map_residue]
  exact (congrArg (IsLocalRing.residue V'.carrier) ((CM.map V V' σ).commutes r)).trans
    (V'.residue_compatible r).symm

theorem geometric_residue (x : V.carrier) :
    V'.residueIso.symm (IsLocalRing.residue V'.carrier (CM.map V V' σ x)) =
      V.residueIso.symm (IsLocalRing.residue V.carrier x) := by
  apply V'.residueIso.injective
  rw [RingEquiv.apply_symm_apply, ← residue_map V V' σ,
    RingEquiv.apply_symm_apply]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationDVRMap.CM
