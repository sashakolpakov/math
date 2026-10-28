import OAI.Analysis.HodgeTheory.Decomposition.RotationExteriorComposition
import OAI.Analysis.HodgeTheory.Decomposition.RotationBracketComposition
import OAI.Analysis.HodgeTheory.Decomposition.ExteriorConstantBracket

/-! # Local Laplacian Boundary -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalLaplacianBoundary.Constructions

noncomputable section

section

/-! The Hodge operator made from the Kähler bracket commutes with
infinitesimal complex rotation, by the proved local differential identities. -/

open scoped ContDiff _root_.Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem complexFormRotation_smoothOn (n : ℕ) (f : E → DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E}
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation n (f y)) U := by
  have hL : ContDiff ℝ ∞ (ComplexRotationDifferentials.Constructions.complexFormRotation (E := E) n) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := DifferentialForms.Manifold.Basic.FormValue E n) (F := DifferentialForms.Manifold.Basic.FormValue E n) (ComplexRotationDifferentials.Constructions.complexFormRotation n)
  have h := hL.comp_contDiffOn hf
  exact h

def localLefschetzLaplacian (n : ℕ) (J : E →L[ℝ] E)
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (K2 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1))
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) (x : E) : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) :=
  extDeriv (ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n J K1 K0 a) x +
    ExteriorConstantBracket.Constructions.lefschetzTwistedBracket (n + 1) J K2 K1 (extDeriv a) x

theorem localLefschetzLaplacian_rotation (b : Module.Basis ι ℝ E) (n : ℕ)
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (K2 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1))
    {U : Set E} (hU : IsOpen U)
    (hK0s : ∀ f : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ (fun y => K0 y (f y)) U)
    (hK1s : ∀ f : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ (fun y => K1 y (f y)) U)
    (hK0r : ∀ y ∈ U, ∀ v, K0 y (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) v) = ComplexRotationDifferentials.Constructions.complexFormRotation n (K0 y v))
    (hK1r : ∀ y ∈ U, ∀ v, K1 y (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1 + 1) v) = ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (K1 y v))
    (hK2r : ∀ y ∈ U, ∀ v, K2 y (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1 + 1 + 1) v) = ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (K2 y v))
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) (ha : ContDiffOn ℝ ∞ a U)
    {x : E} (hx : x ∈ U) :
    ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1)
        (localLefschetzLaplacian n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) K0 K1 K2 a x) =
      localLefschetzLaplacian n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) K0 K1 K2
        (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (a y)) x := by
  let J : E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℂ Complex.I
  let B := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n J K1 K0
  let Bnext := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket (n + 1) J K2 K1
  let H := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n (ContinuousLinearMap.id ℝ E) K1 K0
  let Hnext := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket (n + 1) (ContinuousLinearMap.id ℝ E) K2 K1
  let Ca := fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (a y)
  have hCa : ContDiffOn ℝ ∞ Ca U := complexFormRotation_smoothOn _ a ha
  have hda : ContDiffOn ℝ ∞ (extDeriv a) U := DifferentialForms.Manifold.ExteriorDerivativeSmooth.contDiffOn_extDeriv_of_isOpen ha hU (by simp)
  have hdCa : ContDiffOn ℝ ∞ (extDeriv Ca) U := DifferentialForms.Manifold.ExteriorDerivativeSmooth.contDiffOn_extDeriv_of_isOpen hCa hU (by simp)
  have hdc : ContDiffOn ℝ ∞ (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) J a) U :=
    ExteriorConstantBracket.Constructions.twistedExteriorDerivative_smoothOn _ J a hU ha
  have hCda : ContDiffOn ℝ ∞ (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1 + 1) (extDeriv a y)) U :=
    complexFormRotation_smoothOn _ (extDeriv a) hda
  have hBa : ContDiffOn ℝ ∞ (B a) U := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_smoothOn n J K1 K0 a hU (hK0s a ha) (hK1s _ hdc)
  have hBCa : ContDiffOn ℝ ∞ (B Ca) U := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_smoothOn n J K1 K0 Ca hU (hK0s Ca hCa)
    (hK1s _ (ExteriorConstantBracket.Constructions.twistedExteriorDerivative_smoothOn _ J Ca hU hCa))
  have heqB : (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (B a y) - B Ca y) =ᶠ[𝓝 x] (fun y => -H a y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact LefschetzBracketRotation.Constructions.lefschetzTwistedBracket_rotation b n K0 K1 a hU hy
      (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU ha hy) (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU (hK0s a ha) hy) hK0r (hK1r y hy)
  have hfirst := RotationExteriorComposition.Constructions.rotationExterior_difference b (n + 1) (B a) (B Ca) (H a)
    (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU hBa hx) (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU hBCa hx) heqB
  have heqd : (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1 + 1) (extDeriv a y) - extDeriv Ca y) =ᶠ[𝓝 x]
      (fun y => -CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) J a y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact ComplexRotationDifferentials.Constructions.complexFormRotation_exterior b (n + 1 + 1) a (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU ha hy)
  have hsecond := RotationBracketComposition.Constructions.rotationBracket_difference b (n + 1) K1 K2 (extDeriv a) (extDeriv Ca)
    (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) J a) hU hx
    (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU hda hx) (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU hdCa hx)
    (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU (hK1s _ hda) hx) (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU (hK1s _ hCda) hx)
    (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU (hK1s _ hdCa) hx) hK1r (hK2r x hx) heqd
  have hmixJ := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_anticommute n J K0 K1 K2 a hU hx
    (ha.contDiffAt (hU.mem_nhds hx)) (hK0s a ha) (hK1s _ hdc)
  have hmixId := ExteriorConstantBracket.Constructions.lefschetzBracket_ordinary_anticommute n K0 K1 K2 a hU hx
    (ha.contDiffAt (hU.mem_nhds hx)) (hK0s a ha)
    (hK1s _ (ExteriorConstantBracket.Constructions.twistedExteriorDerivative_smoothOn _ (ContinuousLinearMap.id ℝ E) a hU ha))
  change ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (extDeriv (B a) x + Bnext (extDeriv a) x) =
    extDeriv (B Ca) x + Bnext (extDeriv Ca) x
  rw [map_add]
  apply sub_eq_zero.mp
  calc
    _ = (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (extDeriv (B a) x) - extDeriv (B Ca) x) +
      (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (Bnext (extDeriv a) x) - Bnext (extDeriv Ca) x) := by abel
    _ = (-CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1) J (B a) x - extDeriv (H a) x) +
      (-Hnext (extDeriv a) x - Bnext (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) J a) x) := by rw [hfirst, hsecond]
    _ = -(CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1) J (B a) x + Bnext (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) J a) x) -
      (extDeriv (H a) x + Hnext (extDeriv a) x) := by abel
    _ = 0 := by rw [hmixJ, hmixId, neg_zero, sub_zero]

end

/-! The degree-one boundary of the local Laplacian rotation identity. -/

open scoped ContDiff _root_.Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

def localLefschetzLaplacianZero (J : E →L[ℝ] E)
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E 2 →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E 0)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E 3 →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E 1)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E 1) (x : E) : DifferentialForms.Manifold.Basic.FormValue E 1 :=
  extDeriv (ExteriorConstantBracket.Constructions.lefschetzTwistedBracketZero J K0 a) x + ExteriorConstantBracket.Constructions.lefschetzTwistedBracket 0 J K1 K0 (extDeriv a) x

theorem localLefschetzLaplacianZero_rotation (b : Module.Basis ι ℝ E)
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E 2 →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E 0)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E 3 →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E 1)
    {U : Set E} (hU : IsOpen U)
    (hK0s : ∀ f : E → DifferentialForms.Manifold.Basic.FormValue E 2, ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ (fun y => K0 y (f y)) U)
    (hK0r : ∀ y ∈ U, ∀ v, K0 y (ComplexRotationDifferentials.Constructions.complexFormRotation 2 v) = ComplexRotationDifferentials.Constructions.complexFormRotation 0 (K0 y v))
    (hK1r : ∀ y ∈ U, ∀ v, K1 y (ComplexRotationDifferentials.Constructions.complexFormRotation 3 v) = ComplexRotationDifferentials.Constructions.complexFormRotation 1 (K1 y v))
    (a : E → DifferentialForms.Manifold.Basic.FormValue E 1) (ha : ContDiffOn ℝ ∞ a U) {x : E} (hx : x ∈ U) :
    ComplexRotationDifferentials.Constructions.complexFormRotation 1
        (localLefschetzLaplacianZero (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) K0 K1 a x) =
      localLefschetzLaplacianZero (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) K0 K1
        (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation 1 (a y)) x := by
  let J : E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℂ Complex.I
  let B := ExteriorConstantBracket.Constructions.lefschetzTwistedBracketZero J K0
  let Bnext := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket 0 J K1 K0
  let H := ExteriorConstantBracket.Constructions.lefschetzTwistedBracketZero (ContinuousLinearMap.id ℝ E) K0
  let Hnext := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket 0 (ContinuousLinearMap.id ℝ E) K1 K0
  let Ca := fun y => ComplexRotationDifferentials.Constructions.complexFormRotation 1 (a y)
  have hCa : ContDiffOn ℝ ∞ Ca U := complexFormRotation_smoothOn _ a ha
  have hda : ContDiffOn ℝ ∞ (extDeriv a) U := DifferentialForms.Manifold.ExteriorDerivativeSmooth.contDiffOn_extDeriv_of_isOpen ha hU (by simp)
  have hdCa : ContDiffOn ℝ ∞ (extDeriv Ca) U := DifferentialForms.Manifold.ExteriorDerivativeSmooth.contDiffOn_extDeriv_of_isOpen hCa hU (by simp)
  have hdc : ContDiffOn ℝ ∞ (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 J a) U := ExteriorConstantBracket.Constructions.twistedExteriorDerivative_smoothOn _ J a hU ha
  have hCda : ContDiffOn ℝ ∞ (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation 2 (extDeriv a y)) U :=
    complexFormRotation_smoothOn _ (extDeriv a) hda
  have hBa : ContDiffOn ℝ ∞ (B a) U := hK0s _ hdc
  have hBCa : ContDiffOn ℝ ∞ (B Ca) U := hK0s _ (ExteriorConstantBracket.Constructions.twistedExteriorDerivative_smoothOn _ J Ca hU hCa)
  have heqB : (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation 0 (B a y) - B Ca y) =ᶠ[𝓝 x] (fun y => -H a y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact LefschetzBracketRotation.Constructions.lefschetzTwistedBracket_rotation_zero b K0 a (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU ha hy) (hK0r y hy)
  have hfirst := RotationExteriorComposition.Constructions.rotationExterior_difference b 0 (B a) (B Ca) (H a)
    (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU hBa hx) (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU hBCa hx) heqB
  have heqd : (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation 2 (extDeriv a y) - extDeriv Ca y) =ᶠ[𝓝 x]
      (fun y => -CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 J a y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact ComplexRotationDifferentials.Constructions.complexFormRotation_exterior b 1 a (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU ha hy)
  have hsecond := RotationBracketComposition.Constructions.rotationBracket_difference b 0 K0 K1 (extDeriv a) (extDeriv Ca)
    (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 J a) hU hx
    (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU hda hx) (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU hdCa hx)
    (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU (hK0s _ hda) hx) (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU (hK0s _ hCda) hx)
    (ExteriorConstantBracket.Constructions.smoothField_differentiableAt hU (hK0s _ hdCa) hx) hK0r (hK1r x hx) heqd
  have hmixJ := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_anticommute_zero J K0 K1 a (ha.contDiffAt (hU.mem_nhds hx))
  have hmixId : extDeriv (H a) x + Hnext (extDeriv a) x = 0 := by
    have h := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_anticommute_zero (ContinuousLinearMap.id ℝ E) K0 K1 a
      (ha.contDiffAt (hU.mem_nhds hx))
    simp only [ExteriorConstantBracket.Constructions.directionalExteriorDerivative_twisted, ExteriorConstantBracket.Constructions.directionalExteriorDerivative_id, ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_neg] at h
    exact neg_eq_zero.mp ((neg_add _ _).trans h)
  change ComplexRotationDifferentials.Constructions.complexFormRotation 1 (extDeriv (B a) x + Bnext (extDeriv a) x) = extDeriv (B Ca) x + Bnext (extDeriv Ca) x
  rw [map_add]
  apply sub_eq_zero.mp
  calc
    _ = (ComplexRotationDifferentials.Constructions.complexFormRotation 1 (extDeriv (B a) x) - extDeriv (B Ca) x) +
      (ComplexRotationDifferentials.Constructions.complexFormRotation 1 (Bnext (extDeriv a) x) - Bnext (extDeriv Ca) x) := by abel
    _ = (-CovectorSymbolAction.Constructions.twistedExteriorDerivative 0 J (B a) x - extDeriv (H a) x) +
      (-Hnext (extDeriv a) x - Bnext (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 J a) x) := by rw [hfirst, hsecond]
    _ = -(CovectorSymbolAction.Constructions.twistedExteriorDerivative 0 J (B a) x + Bnext (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 J a) x) -
      (extDeriv (H a) x + Hnext (extDeriv a) x) := by abel
    _ = 0 := by rw [hmixJ, hmixId, neg_zero, sub_zero]

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalLaplacianBoundary.Constructions
