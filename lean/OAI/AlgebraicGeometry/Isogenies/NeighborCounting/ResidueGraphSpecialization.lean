import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryKernelSpecialization
import Mathlib.Algebra.CharP.Algebra

/-! # Residue Graph Specialization -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The original residue-field isomorphism supplies characteristic q
and perfectness, so graph-character specialization needs no extra
Frobenius or residue-field hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] (q : ℕ) [Fact q.Prime]
  (A : Grp (Over (Spec (.of R)))) (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)
  (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

include ρ in
theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.character_specializes_zero_of_residueIso
    {H : Over (Spec (.of R))} [Etale H.hom] (χ : H ⟶ C.identity.X) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map χ = 1 := by
  let : CharP (IsLocalRing.ResidueField R) q :=
    charP_of_injective_ringHom (f := ρ.toRingHom) ρ.injective q
  let : IsAlgClosed (IsLocalRing.ResidueField R) :=
    IsAlgClosed.of_ringEquiv (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) _ ρ
  exact OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.character_specializes_zero R L q A C χ

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
