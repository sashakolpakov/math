import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesIs
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.RingHom.Flat

/-! # Power Series X -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesX.Construction.PowerSeriesFlatShift

noncomputable section

/-! Flat formal coordinate rings centered at an arbitrary rational point. -/

variable {σ K : Type*} [CommRing K]

def translateMap (v : σ → K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (v i))

theorem translateMap_comp_neg (v : σ → K) :
    (translateMap (-v)).comp (translateMap v) = AlgHom.id K (MvPolynomial σ K) := by
  ext i
  simp [translateMap]

def translate (v : σ → K) : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K where
  __ := translateMap v
  invFun := translateMap (-v)
  left_inv p := AlgHom.congr_fun (translateMap_comp_neg v) p
  right_inv p := by simpa using AlgHom.congr_fun (translateMap_comp_neg (-v)) p

def map (v : σ → K) : MvPolynomial σ K →ₐ[K] MvPowerSeries σ K :=
  (MvPolynomial.coeToMvPowerSeries.algHom K).comp (translate v).toAlgHom

theorem map_X (v : σ → K) (i : σ) :
    map v (MvPolynomial.X i) = MvPowerSeries.X i + MvPowerSeries.C (v i) := by
  simp [map, translate, translateMap]

theorem constantCoeff_map (v : σ → K) (p : MvPolynomial σ K) :
    MvPowerSeries.constantCoeff (map v p) = MvPolynomial.eval v p := by
  have he : MvPowerSeries.constantCoeff.comp (map v).toRingHom = MvPolynomial.eval v := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [map, translate, translateMap, MvPowerSeries.algebraMap_apply]
    · intro i
      simp [map_X]
  exact RingHom.congr_fun he p

variable [Finite σ] [IsNoetherianRing K]

theorem canonical_flat : Module.Flat (MvPolynomial σ K) (MvPowerSeries σ K) :=
  Module.Flat.of_linearEquiv (MvPowerSeries.toAdicCompletionAlgEquiv σ K).toLinearEquiv

theorem flat (v : σ → K) : (map v).toRingHom.Flat := by
  have hf : (MvPolynomial.coeToMvPowerSeries.algHom (σ := σ) (R := K) K).toRingHom.Flat := by
    change Module.Flat (MvPolynomial σ K) (MvPowerSeries σ K)
    exact canonical_flat
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (translate v).bijective) hf

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesX.Construction.PowerSeriesFlatShift
