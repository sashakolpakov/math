import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CentralTypeTranslation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NormalizedCentral

/-! # Identity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Identity.CM.OrdinaryHecke

noncomputable section

/-! The same three rational operators whose character values are obtained
from radial parameters equal the actual raw ordinary-neighbor basis
operators, including every inactive multiplicative block. -/

open scoped Classical
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NormalizedCentral
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CentralTypeTranslation.CM

variable {s : ℕ} (active : Fin s) (fullSide : Fin s → Bool)

def minusculeIndex (i : Fin 3) : Fin 4 := ⟨i.val + 1, by omega⟩

theorem neighbor_type (i : Fin 3) :
    CentralTypeTranslation.CM.shifted (CMExtraction.Intrinsic.MinusculeParameters.activeMinusculeType active (minusculeIndex i))
      (AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents active fullSide) 1 (i.val + 1) =
        Neighbor.Types.CM.localType active fullSide i := by
  unfold CentralTypeTranslation.CM.shifted Neighbor.Types.CM.localType CMExtraction.Intrinsic.MinusculeParameters.activeMinusculeType
  simp only [one_mul, add_zero, Isogenies.NeighborCounting.HeckeExponents.neighborLevel]
  congr 1
  funext v k
  by_cases hv : v = active
  · subst v
    simp [AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents, Isogenies.NeighborCounting.HeckeExponents.neighborExponents, Isogenies.NeighborCounting.HeckeExponents.activeExponents, Isogenies.NeighborCounting.HeckeExponents.neighborLevel, minusculeIndex]
  · cases hs : fullSide v <;>
      simp [AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents, Isogenies.NeighborCounting.HeckeExponents.neighborExponents, hv, hs, Isogenies.NeighborCounting.HeckeExponents.neighborLevel, minusculeIndex]

theorem raw_operator (q : ℕ) [Fact q.Prime]
    (basis : AbelianScheme.TateComparison.Local.LocalType s → AbelianScheme.TateComparison.HeckeKernel.Hecke s q)
    (hb : ∀ t, AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AbelianScheme.TateComparison.HeckeKernel.representative s q t) (basis t))
    (i : Fin 3) :
    AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q active fullSide ^ (i.val + 1) *
      basis (CMExtraction.Intrinsic.MinusculeParameters.activeMinusculeType active (minusculeIndex i)) =
        basis (Neighbor.Types.CM.integralType active fullSide i).val := by
  exact (CentralTypeTranslation.CM.basis_translation q basis hb (CMExtraction.Intrinsic.MinusculeParameters.activeMinusculeType active (minusculeIndex i))
    (AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0Exponents active fullSide) 1 (i.val + 1)).trans
      (congrArg basis (neighbor_type active fullSide i))

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
  (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)

include hA in
theorem native_operator (i : Fin 3) :
    CMExtraction.Intrinsic.NormalizedCentral.nativeAbsorbedHecke D A fullSide i =
      A.basis (Neighbor.Types.CM.integralType D.pel.reference.distinguished fullSide i).val := by
  have h := raw_operator D.pel.reference.distinguished fullSide q A.basis hA.basis i
  fin_cases i
  · change AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide * CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D.pel A 1 = _
    simpa [minusculeIndex, CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke] using h
  · change AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide ^ 2 * CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D.pel A 2 = _
    exact h
  · change AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide ^ 3 * AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.pel.reference.distinguished = _
    rw [← CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke_three D.pel A hg hq hIsogenyQuotient hA]
    exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Identity.CM.OrdinaryHecke
