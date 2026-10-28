import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyNewton
import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.TensorNilpotence

/-! # Family Tensor Nilpotence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyTensorNilpotence.ProjectiveK

noncomputable section

/-! Arbitrarily many actual invertible-sheaf tensor differences are jointly
nilpotent in the coherent Hilbert filtration. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] [Infinite K] {r : ℕ} {A : Scheme.{u}} [IsIntegral A]
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f] (j : Fin (r + 1))

theorem coherentTensorDifference_family_eq_zero {s : ℕ}
    (L : Fin s → A.Modules) (hL : ∀ i, AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible (L i))
    (a : Fin s → ℕ) (d : ℕ) (hd : d ≤ ∑ i, a i) (x : Coherent.KTheory.Projective.CoherentK0 A)
    (hx : x ∈ Coherent.HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j d) :
    FamilyNewton.Family.ordered (fun i => Coherent.KTheory.Projective.coherentTensorDifference (L i) (hL i)) a x = 0 :=
  FamilyNewton.Family.ordered_eq_zero_of_filtration (Coherent.HilbertFiltration.ProjectiveK.coherentHilbertFiltration f j)
    (Coherent.HilbertFiltration.ProjectiveK.coherentHilbertFiltration_zero f j) _
    (fun i => Coherent.TensorNilpotence.ProjectiveK.coherentTensorDifference_mem_hilbertFiltration f j (L i) (hL i)) a x
    (Coherent.HilbertFiltration.ProjectiveK.coherentHilbertFiltration_mono f j hd hx)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyTensorNilpotence.ProjectiveK
