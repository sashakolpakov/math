import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.RelativeDiagonal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnramifiedDiagonalIdeal
import Mathlib.Data.List.FinRange

/-! # Diagonal Sequence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.DiagonalSequence

noncomputable section

/-! At any local point of the diagonal of an algebra etale over a
polynomial ring in n variables, the native diagonal ideal is generated
by a regular sequence of exactly n coordinate differences. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u

open _root_.MvPolynomial RingTheory.Sequence OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DiagonalParameters

variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) K) A] [IsScalarTower K (MvPolynomial (Fin n) K) A]

local notation "P" => MvPolynomial (Fin n) K
local notation "φ" => IsScalarTower.toAlgHom K P A

variable (L : Type u) [CommRing L] (g : A ⊗[K] A →+* L)

def sequence : List L := (List.finRange n).map fun i => g (Smooth.DiagonalParameters.parameter K A (Fin n) φ i)

theorem length : (sequence K A n L g).length = n := by simp [sequence]

theorem ideal [IsNoetherianRing L] [IsLocalRing L] [Algebra.FormallyUnramified P A]
    (hp : (KaehlerDifferential.ideal K A).map g ≠ ⊤) :
    (KaehlerDifferential.ideal K A).map g = Ideal.ofList (sequence K A n L g) := by
  have h := UnramifiedDiagonalIdeal.localized K P A L g hp
  have hk := Polynomial.RelativeDiagonal.kernel K A (Fin n)
  change RingHom.ker (Relative.TensorKernel.map K P A).toRingHom =
    Polynomial.RelativeDiagonal.ideal K A (Fin n) at hk
  rw [hk] at h
  refine h.trans ?_
  unfold Polynomial.RelativeDiagonal.ideal
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext x
  simp [sequence]

theorem regular [IsLocalRing L] [Module.Flat P A]
    (hg : g.Flat) (hp : (KaehlerDifferential.ideal K A).map g ≠ ⊤) :
    IsRegular L (sequence K A n L g) := by
  apply Smooth.DiagonalParameters.regular K A (Fin n) φ
    (RingHom.flat_algebraMap_iff.mpr (inferInstanceAs (Module.Flat P A))) L g hg
    (List.finRange n) (List.nodup_finRange n)
  intro i _
  apply IsLocalRing.le_maximalIdeal hp
  apply Ideal.mem_map_of_mem
  exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal K (φ (X i))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.DiagonalSequence
