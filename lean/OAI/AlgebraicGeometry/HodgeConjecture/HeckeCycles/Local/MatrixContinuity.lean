import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur

/-! # Matrix Continuity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixContinuity.CM

noncomputable section

/-! Continuity of finite-coordinate matrices and their actual local
unitary blocks, used to extend rational identities by density. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local

variable {X I : Type*} [TopologicalSpace X] [Fintype I] [DecidableEq I]

theorem of_action {R : Type*} [Semiring R] [TopologicalSpace R]
    (M : X → Matrix I I R) (h : ∀ v : I → R, Continuous (fun x => M x *ᵥ v)) : Continuous M := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_apply i).comp (h (Pi.single j 1))).congr
    (fun x => by simp [Matrix.mulVec_single])

omit [Fintype I] [DecidableEq I] in
theorem padic {q : ℕ} [Fact q.Prime]
    (M : X → Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (h : Continuous M) :
    Continuous (fun x => (M x).map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom) :=
  h.matrix_map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection_continuous q)

variable {Place : Type} [Fintype Place] [DecidableEq Place]
  {n q : ℕ} [Fact q.Prime] (c : (Place × Fin 3) ≃ Fin n)

theorem blocks (b : X → Place → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (hb : Continuous b) :
    Continuous (fun x => (CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (b x)).val) := by
  apply of_action
  intro v
  apply continuous_pi
  intro i
  cases i with
  | inl p =>
      have hc := ((continuous_subtype_val.comp ((continuous_apply p.1).comp hb)).matrix_mulVec
        (show Continuous (fun _ : X => fun j => v (Sum.inl (p.1, j))) from continuous_const))
      exact ((continuous_apply p.2).comp hc).congr
        (fun x => (CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic_inl c (b x) v p.1 p.2).symm)
  | inr p =>
      have hc := ((continuous_subtype_val.comp (((continuous_apply p.1).comp hb).inv)).matrix_transpose.matrix_mulVec
        (show Continuous (fun _ : X => fun j => v (Sum.inr (p.1, j))) from continuous_const))
      exact ((continuous_apply p.2).comp hc).congr
        (fun x => (CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic_inr c (b x) v p.1 p.2).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixContinuity.CM
