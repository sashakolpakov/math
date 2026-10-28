import OAI.Analysis.Fourier.WavePackets.PeriodicDirichlet

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Concentration
open scoped ContDiff Topology ComplexOrder

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V} {b : Basis ι ℝ P}

/-- The extra periodic coordinates preserve every fixed-data hypothesis
of the general Dirichlet theorem. -/
def PeriodicQuaternionicData.padFourth (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b) :
    PeriodicQuaternionicData (P := P × (Fin m → ℝ)) (V := V) (ι := ι ⊕ Fin m)
      OAI.Analysis.Calculus.Quaternion.fourSlots (paddedLatticeSplit e) (paddedLatticeBasis (m := m) b) where
  dimension := D.dimension
  defining x := D.defining (dropFourth m x)
  background x := D.background (dropFourth m x)
  density x := D.density (dropFourth m x)
  transverse := D.transverse
  compact := D.compact
  bounded x hx := D.bounded _ hx
  defining_smooth := D.defining_smooth.comp (dropFourth m).contDiff
  background_smooth := D.background_smooth.comp (dropFourth m).contDiff
  density_smooth := D.density_smooth.comp (dropFourth m).contDiff
  defining_periodic := latticePeriodic_dropFourth e b D.defining_periodic
  background_periodic := latticePeriodic_dropFourth e b D.background_periodic
  density_periodic := latticePeriodic_dropFourth e b D.density_periodic
  regular x hx hzero := by
    apply D.regular _ hx
    ext v
    have hz := congrArg (fun L : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 →L[ℝ] ℝ => L (insertFourth m v)) hzero
    have hd := fderiv_comp x (D.defining_smooth.differentiable (by simp) _)
      (dropFourth m).differentiableAt
    change fderiv ℝ (fun y => D.defining (dropFourth m y)) x = _ at hd
    rw [hd] at hz
    simpa only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
      dropFourth_insertFourth, zero_apply] using hz
  defining_positive x hx := by
    rw [quaternionHessian_dropFourth (D.defining_smooth.of_le (by simp))]
    exact D.defining_positive _ hx
  background_nonnegative x hx := by
    rw [quaternionHessian_dropFourth (D.background_smooth.of_le (by simp))]
    exact D.background_nonnegative _ hx
  background_degenerate x hx := by
    rw [quaternionHessian_dropFourth (D.background_smooth.of_le (by simp))]
    exact D.background_degenerate _ hx
  density_positive x hx := D.density_positive _ hx

theorem PeriodicQuaternionicSolution.dummy_translation
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b)
    (S : PeriodicQuaternionicSolution (m := m) (s := 4) (slots := OAI.Analysis.Calculus.Quaternion.fourSlots)
      (P := P × (Fin m → ℝ)) (V := V) (ι := ι ⊕ Fin m)
      (e := paddedLatticeSplit e) (b := paddedLatticeBasis (m := m) b) D.padFourth)
    (d : Fin m → ℝ) : ∀ x, D.defining (dropFourth m x) ≤ 0 →
      S.u (fourthInjection m d + x) = S.u x := by
  apply dirichlet_translation_invariance (m := m) (P := P × (Fin m → ℝ))
    (V := V) (ι := ι ⊕ Fin m) D.dimension
    (paddedLatticeSplit e) (paddedLatticeBasis (m := m) b) D.compact
    (D.padFourth.defining_smooth.of_le (by simp))
    (D.padFourth.background_smooth.of_le (by simp)) (S.smooth.of_le (by simp))
    D.padFourth.bounded D.padFourth.defining_periodic D.padFourth.background_periodic S.periodic
    (fun x hx => D.padFourth.defining_positive x hx.le) S.admissible S.equation S.boundary
  all_goals intro x; simp only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth, map_add,
    dropFourth_fourthInjection, zero_add]

theorem PeriodicQuaternionicSolution.independent_fourth
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b)
    (S : PeriodicQuaternionicSolution (m := m) (s := 4) (slots := OAI.Analysis.Calculus.Quaternion.fourSlots)
      (P := P × (Fin m → ℝ)) (V := V) (ι := ι ⊕ Fin m)
      (e := paddedLatticeSplit e) (b := paddedLatticeBasis (m := m) b) D.padFourth)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4) (hx : D.defining (dropFourth m x) ≤ 0) :
    S.u x = S.u (insertFourth m (dropFourth m x)) := by
  have he := S.dummy_translation D (fourthCoordinates m x) (insertFourth m (dropFourth m x))
    (by simpa only [dropFourth_insertFourth] using hx)
  rw [add_comm, insertFourth_dropFourth_add] at he
  exact he

end OAI.Analysis.Fourier.WavePackets
