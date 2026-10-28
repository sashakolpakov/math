import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TypedKernelTorsion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Assembly

/-! # Active Choice Torsion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveChoiceTorsion

noncomputable section

/-! Every original active choice is killed by q on all test schemes,
even though its native ambient torsion has multiplier q^i. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TypedKernelTorsion

variable {L : Type} [Field L] [CharZero L] {g s : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of L))) (q : ℕ) [Fact q.Prime]
  (active : Fin s) (multiplicative : Fin s → Bool) (i : Fin 3)
  {P : Over (Spec (.of L))}

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance activeModule : Module (ZMod (q ^ HeckeExponents.neighborLevel i))
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents active multiplicative i active)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents active multiplicative i active)
    (HeckeExponents.neighborExponents_bound active multiplicative i active)

theorem activeChoice_killed
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice A.scheme (q ^ HeckeExponents.neighborLevel i)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents active multiplicative i active)) P)
    (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0}) : F.subgroup.KilledBy q := by
  obtain ⟨R⟩ := F.geometric
  have ht := AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.scheme) (𝟙 (Spec (.of L)))
    (q ^ HeckeExponents.neighborLevel i) (pow_pos (Fact.out : q.Prime).pos _) hTorsionQuotient
  apply TypedKernelTorsion.killedBy_of_moduleType F.subgroup R (q ^ HeckeExponents.neighborLevel i) q F.killed ht.2 _ F.moduleType
  rw [HeckeExponents.neighborExponents_active]
  exact HeckeExponents.activeElementaryModule_killed q i

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveChoiceTorsion
