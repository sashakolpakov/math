import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices

/-! # Single Block Phase -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SingleBlockPhase.CM

noncomputable section

/-! A single unitary block gives exactly the indexed finite
symplectic matrix used by the radial Hecke action. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (c : (Place × Fin 3) ≃ Fin n) (μ : Place)

theorem linear (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) : CMExtraction.BlockFamilyMatrices.Local.blockFamilyGL c (Pi.mulSingle μ g) = CMExtraction.ActiveBlockMatrices.Local.activeBlockGL c μ g := by
  apply Units.ext
  have hb : (fun i : Place => ((Pi.mulSingle μ g : Place → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) i).val) =
      (fun i => if i = μ then g.val else (1 : Matrix (Fin 3) (Fin 3) ℚ_[q])) := by
    funext i
    by_cases hi : i = μ
    · subst i
      simp
    · simp [hi]
  exact congrArg (fun f => Matrix.reindex ((Equiv.prodComm (Fin 3) Place).trans c)
    ((Equiv.prodComm (Fin 3) Place).trans c) (Matrix.blockDiagonal f)) hb

theorem local_matrix (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (Pi.mulSingle μ g) =
      RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex c.symm (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
        (CMExtraction.ActiveBlockMatrices.Local.activeBlockGL c μ (CMExtraction.Contragredient.Local.contragredient ℚ_[q] g)))) := by
  have he : (fun i : Place => CMExtraction.Contragredient.Local.contragredient ℚ_[q] ((Pi.mulSingle μ g : Place → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) i)) =
      Pi.mulSingle μ (CMExtraction.Contragredient.Local.contragredient ℚ_[q] g) := by
    funext i
    by_cases hi : i = μ
    · subst i
      simp
    · simp [hi]
  exact congrArg (fun A => RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex c.symm (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic A)))
    ((congrArg (CMExtraction.BlockFamilyMatrices.Local.blockFamilyGL c) he).trans (linear q c μ (CMExtraction.Contragredient.Local.contragredient ℚ_[q] g)))

theorem finite (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q (CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (Pi.mulSingle μ g)) =
      RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (CMExtraction.ActiveBlockMatrices.Local.activeBlockGL c μ (CMExtraction.Contragredient.Local.contragredient ℚ_[q] g))) :=
  congrArg (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q) (local_matrix q c μ g)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SingleBlockPhase.CM
