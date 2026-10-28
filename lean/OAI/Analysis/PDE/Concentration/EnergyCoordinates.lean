import OAI.Analysis.PDE.Concentration.Cylinder.Estimate
import OAI.Analysis.PDE.Concentration.ActualEnergy

namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green InnerProductSpace Laplacian Set
open scoped ContDiff

/-- Identification of the three physical time coordinates with the energy
construction's one-row time block. -/
noncomputable def cylinderEnergyEquiv : CylinderSpace ≃ₗᵢ[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.uniqueProd (Fin 3) (Fin 1)).symm

@[simp] theorem cylinderEnergyEquiv_apply (x : CylinderSpace) (i : Fin 1) (j : Fin 3) :
    cylinderEnergyEquiv x (i, j) = x j := rfl

theorem energyComplexTime_cylinderEnergyEquiv (x : CylinderSpace) :
    OAI.Analysis.PDE.Green.energyComplexTime (cylinderEnergyEquiv x) = (cylinderComplexEquiv x).2 := by
  simp [OAI.Analysis.PDE.Green.energyComplexTime, cylinderComplexEquiv_apply, mul_comm]

theorem cylinderEnergyEquiv_preimage_annulus (a : ℝ) :
    cylinderEnergyEquiv ⁻¹' physicalEnergyAnnulus a = cylinderAnnulus a := by
  ext x
  simp only [mem_preimage, physicalEnergyAnnulus, cylinderAnnulus,
    energyComplexTime_cylinderEnergyEquiv, Set.mem_ofPred_eq]

theorem laplacian_comp_cylinderEnergyEquiv (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ) (x : CylinderSpace) :
    Δ (f ∘ cylinderEnergyEquiv) x = Δ f (cylinderEnergyEquiv x) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (b.map cylinderEnergyEquiv)]
  dsimp only
  have hd : iteratedFDeriv ℝ 2 (f ∘ cylinderEnergyEquiv) x =
      (iteratedFDeriv ℝ 2 f (cylinderEnergyEquiv x)).compContinuousLinearMap
        (fun _ => cylinderEnergyEquiv.toContinuousLinearEquiv.toContinuousLinearMap) := by
    simpa only [preimage_univ, iteratedFDerivWithin_univ,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      cylinderEnergyEquiv.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right
        f uniqueDiffOn_univ (Set.mem_univ (cylinderEnergyEquiv x)) 2
  rw [hd]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, OrthonormalBasis.map_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem contDiffOn_comp_cylinderEnergyEquiv {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ} {a : ℝ}
    (hf : ContDiffOn ℝ ∞ f (physicalEnergyAnnulus a)) :
    ContDiffOn ℝ ∞ (f ∘ cylinderEnergyEquiv) (cylinderAnnulus a) := by
  have h := hf.comp_continuousLinearMap
    cylinderEnergyEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    cylinderEnergyEquiv_preimage_annulus a] using h

end OAI.Analysis.PDE.Concentration
