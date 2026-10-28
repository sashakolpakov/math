import OAI.AlgebraicGeometry.GroupSchemes.GeometricKernel
import OAI.AlgebraicGeometry.GroupSchemes.Cartier

/-! # Connected Step -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! The local/local first-level obstruction for the actual geometric tower. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv
open OAI.AlgebraicGeometry.GroupSchemes.LocalObstruction.FiniteEtale

universe u
variable {k : Type u} [Field k]

open OAI.AlgebraicGeometry.GroupSchemes.KernelIdeal.FiniteEtale

/-- The coordinate ideal from the geometric kernel is the convolution multiplication ideal. -/
theorem ConnectedStep.FiniteEtale.first_kernel_convolution {p h : ℕ} (G : FiniteEtale.PDivisibleGroup k p h) :
    letI := (G.level 2).coordinateHopf
    letI := (G.level 2).coordinateCoalgebra
    RingHom.ker (FiniteEtale.FiniteCommGroupScheme.coordinateMap (G.inclusion 1)).toRingHom =
      LocalObstruction.FiniteEtale.multiplicationKernelIdeal k p (G.level 2).algebra := by
  let := (G.level 2).coordinateHopf
  let := (G.level 2).coordinateCoalgebra
  rw [G.first_kernel_ideal]
  change Ideal.span ((G.level 2).coordinatePower p ''
    (RingHom.ker (G.level 2).coordinateAugmentation.toRingHom : Set (G.level 2).algebra)) = _
  simp only [LocalObstruction.FiniteEtale.multiplicationKernelIdeal, LocalObstruction.FiniteEtale.augmentationIdeal,
    FiniteEtale.FiniteCommGroupScheme.coordinatePower_apply, FiniteEtale.FiniteCommGroupScheme.coordinateAugmentation]
  rfl

/-- A height-one tower cannot have a local second level and local dual first level. -/
theorem FiniteEtale.PDivisibleGroup.not_local_local {p : ℕ} [Fact p.Prime] [CharP k p]
    [PerfectRing k p] (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsecond : IsLocalRing (G.level 2).algebra)
    (hdual : IsLocalRing (G.level 1).cartierDual.algebra) : False := by
  have hdim2 : p < Module.finrank k (G.level 2).algebra := by
    rw [G.rank]
    have hp := (Fact.out : p.Prime).two_le
    simp only [mul_one, pow_two]
    nlinarith
  have hdim1 : Module.finrank k (G.level 1).algebra = p := by
    simpa only [mul_one, pow_one] using G.rank 1
  exact @LocalObstruction.FiniteEtale.no_local_local_prime_step k _ p _ _ (G.level 2).algebra (G.level 1).algebra
    _ _ (G.level 2).coordinateHopf (G.level 1).coordinateHopf
    (G.level 2).coordinateHopf_cocomm (G.level 1).coordinateHopf_cocomm
    (G.level 2).finite (G.level 1).finite _ hsecond hdual
    hdim2 hdim1 (FiniteEtale.FiniteCommGroupScheme.coordinateBialgMap (G.inclusion 1)) (ConnectedStep.FiniteEtale.first_kernel_convolution G)

end

end OAI.AlgebraicGeometry.GroupSchemes
