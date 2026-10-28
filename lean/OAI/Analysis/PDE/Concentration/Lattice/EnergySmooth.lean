import OAI.Analysis.PDE.Concentration.Lattice.FiberMap

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped ContDiff Matrix.Norms.Elementwise

theorem integral_continuousLinearEquiv_image
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    (L : E ≃L[ℝ] E) {S : Set E} (hS : MeasurableSet S) (f : E → ℝ) :
    (∫ x in L '' S, f x) = |L.toLinearEquiv.toLinearMap.det| * ∫ y in S, f (L y) := by
  have hh := integral_image_eq_integral_abs_det_fderiv_smul volume
    (f := fun x => L x) (f' := fun _ => L.toContinuousLinearMap) (s := S) hS
    (fun x hx => L.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)
    L.injective.injOn f
  rw [hh]
  simp only [smul_eq_mul, integral_const_mul]
  rfl

theorem physicalLatticeEnergy_integral {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ) (ha : 0 < a)
    (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ))
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) :
    OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a) A B u z =
      |(spatialFiberEquiv (sideHundredLattice (spatialFramePi R))).toLinearEquiv.toLinearMap.det| *
        ∫ y in OAI.Analysis.PDE.Green.physicalSpatialFiber d a (OAI.Analysis.PDE.Green.energyComplexTime z),
          OAI.Analysis.PDE.Green.combinedEnergyDensity e lam A B u (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z
            (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) y)) := by
  have hs : MeasurableSet (OAI.Analysis.PDE.Green.physicalSpatialFiber d a (OAI.Analysis.PDE.Green.energyComplexTime z)) :=
    (measurableSet_Icc.prod (OAI.Analysis.PDE.Green.isOpen_physical_fiber a (OAI.Analysis.PDE.Green.energyComplexTime z) ha hz).measurableSet).preimage
      (OAI.Analysis.PDE.Green.physicalSpatialEquiv d).measurable
  unfold OAI.Analysis.PDE.Green.setFiberCombinedEnergy
  rw [physicalLatticeEnergyCell_fiber]
  exact integral_continuousLinearEquiv_image _ hs _

/-- Smoothness is proved for the actual rotated-lattice energy integral;
no regularity of the energy function itself is assumed. -/
theorem contDiffOn_physicalLatticeCombinedEnergy {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ) (ha : 0 < a)
    (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ)}
    (hA : ContDiff ℝ ∞ A) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hB : ContDiff ℝ ∞ B) (hu : ContDiff ℝ ∞ u) :
    ContDiffOn ℝ ∞ (OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a) A B u)
      {z | a < ‖OAI.Analysis.PDE.Green.energyComplexTime z‖} := by
  let L := spatialFiberEquiv (sideHundredLattice (spatialFramePi R))
  have hf : ContDiff ℝ ∞ (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 =>
      OAI.Analysis.PDE.Green.combinedEnergyDensity e lam A B u (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 p.1 (L p.2))) := by
    exact (OAI.Analysis.PDE.Green.contDiff_combinedEnergyDensity e lam hA hB hu).comp
      ((OAI.Analysis.PDE.Green.contDiff_fiberEmbedding (d + 1) 3 ∞).comp
        (contDiff_fst.prodMk (L.contDiff.comp contDiff_snd)))
  have hh := OAI.Analysis.PDE.Green.contDiffOn_real_physical_fiber_integral a ha OAI.Analysis.PDE.Green.energyComplexTime
    (OAI.Analysis.PDE.Green.contDiff_energyComplexTime ∞) _ hf
  apply (contDiffOn_const.mul hh).congr
  intro z hz
  exact physicalLatticeEnergy_integral R a ha e lam A B u z hz.le

end OAI.Analysis.PDE.Concentration
