import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagEndpointTransfer
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConvolutionMultiplier
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricSplitFrame

/-! # Geometric Convolution -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The raw spherical convolution coefficients are the actual geometric
neighbor multiplicities, through the actual IsogenyQuotient flag correspondence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

theorem GeometricConvolution.convolutionCoefficients_multiplierNat {s q : ℕ} [Fact q.Prime]
    (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (u v w : Local.IntegralType s)
    (hw : ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v w ≠ 0) :
    w.multiplierNat = u.multiplierNat + v.multiplierNat := by
  apply Int.natCast_inj.mp
  push_cast
  simp only [Local.IntegralType.multiplierNat_cast]
  exact ConvolutionMultiplier.convolutionCoefficients_multiplier s q hElementaryDivisors u v w hw

theorem Data.SphericalPELAlbaneseData.flagMultiplier_single {s : ℕ} (t : Local.IntegralType s) :
    Data.SphericalPELAlbaneseData.flagMultiplier [t] (Fin.last [t].length) = t.multiplierNat := by
  simp [Data.SphericalPELAlbaneseData.flagMultiplier, Local.cumulativeMultiplier, Local.IntegralType.multiplierNat]

theorem Data.SphericalPELAlbaneseData.flagMultiplier_pair {s : ℕ} (u v : Local.IntegralType s) :
    Data.SphericalPELAlbaneseData.flagMultiplier [u, v] (Fin.last [u, v].length) = u.multiplierNat + v.multiplierNat := by
  change (u.val.multiplier + (v.val.multiplier + 0)).toNat = _
  rw [add_zero]
  exact Int.toNat_add u.property.1 v.property.1

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

section Frame
variable {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} (x : D.GeometricPoint b)
  (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)

include hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors hf in
theorem Data.SphericalPELAlbaneseData.neighbors_eq_lattice_map (t : Local.IntegralType s) :
    D.neighbors t b x =
      (ChosenLatticeNeighbors.chosenLatticeNeighbors s q t (fun v => D.framedFiberSourceLattice b x frame (v, false))).map
        (D.geometricLatticeTarget x frame t.multiplierNat) := by
  rw [← D.geometricFlagEndpoints_single b x t,
    D.geometricFlagEndpoints_eq_lattice_map hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors x frame hf,
    LinearFlagEndpoints.linearFlagEndpoints_single, Data.SphericalPELAlbaneseData.flagMultiplier_single]

include hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors hf in
theorem Data.SphericalPELAlbaneseData.neighbors_convolution_in_frame (u v : Local.IntegralType s) :
    (D.neighbors u b x).bind (D.neighbors v b) =
      (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n => n • D.neighbors w b x) := by
  let L₀ := fun i => D.framedFiberSourceLattice b x frame (i, false)
  let f := D.geometricLatticeTarget x frame (u.multiplierNat + v.multiplierNat)
  have h := congrArg (LatticeCosetConvolution.multisetMapHom f) (ChosenLatticeNeighbors.chosenLatticeNeighbors_convolution s q hElementaryDivisors u v L₀)
  simp only [map_finsuppSum, map_nsmul] at h
  rw [← D.geometricFlagEndpoints_pair b x u v,
    D.geometricFlagEndpoints_eq_lattice_map hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors x frame hf,
    LinearFlagEndpoints.linearFlagEndpoints_pair, Data.SphericalPELAlbaneseData.flagMultiplier_pair]
  refine h.trans ?_
  apply Finsupp.sum_congr
  intro w hw
  have hm := GeometricConvolution.convolutionCoefficients_multiplierNat hElementaryDivisors u v w (Finsupp.mem_support_iff.mp hw)
  change _ • (ChosenLatticeNeighbors.chosenLatticeNeighbors s q w L₀).map f = _
  rw [D.neighbors_eq_lattice_map hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors x frame hf w]
  congr 2
  exact congrArg (D.geometricLatticeTarget x frame) hm.symm

end Frame

include hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.neighbors_convolution (u v : Local.IntegralType s)
    {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b) :
    (D.neighbors u b x).bind (D.neighbors v b) =
      (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n => n • D.neighbors w b x) := by
  have := FiberLattices.charZero_of_field_spec_map b
  exact D.neighbors_convolution_in_frame hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors x
    (D.geometricSplitFrame hg hdegree hs hgeometry b x)
    (D.geometricSplitFrame_equivariant hg hdegree hs hgeometry b x) u v

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
