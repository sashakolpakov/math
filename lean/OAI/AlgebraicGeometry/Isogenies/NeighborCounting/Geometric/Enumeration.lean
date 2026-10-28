import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.ActiveChoices
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.CompactChoices
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ChoiceTypeTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Choices

/-! # Enumeration -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.Enumeration.Neighbor

noncomputable section

/-! Enumerate the original complete chosen-block tuple. Compact
coordinates have one constructed choice each; the active coordinate is
the subspace of the prescribed dimension. Every original choice appears
once, and the active relative subgroup is retained literally. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Choices.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.ActiveChoices OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.CompactChoices OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ChoiceTypeTransport

def zeroComponentEquiv {s : ℕ} (C : Fin (s + 1) → Type*)
    (c : ∀ v : Fin s, C v.succ) (hc : ∀ v (a : C v.succ), a = c v) :
    (∀ v, C v) ≃ C 0 where
  toFun f := f 0
  invFun a := Fin.cases a c
  left_inv f := funext fun v => Fin.cases rfl (fun w => (hc w (f w.succ)).symm) v
  right_inv _ := rfl

variable {S : Scheme} {A : Over S} [GrpObj A] [IsCommMonObj A]
  (q : ℕ) [Fact q.Prime] {s : ℕ} (c : Fin s → Bool) (i : Fin 3)
  (p : Fin (s + 1) → (A ⟶ A)) [∀ v, IsMonHom (p v)]
  (K : Type) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S)
  [∀ v, IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v)).hom]
  [∀ v, Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v)).hom]

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : Fact (1 ≤ HeckeExponents.neighborLevel i) := ⟨by unfold HeckeExponents.neighborLevel; omega⟩

local instance neighborModule (v : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false c) i v)

local instance activeModule : Module (ZMod (q ^ HeckeExponents.neighborLevel i))
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i) (HeckeExponents.activeExponents i)
    (fun k => (HeckeExponents.activeExponents_bound i k).trans (by unfold HeckeExponents.neighborLevel; omega))

local instance compactModule (v : Fin s) : Module (ZMod (q ^ HeckeExponents.neighborLevel i))
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if c v then HeckeExponents.neighborLevel i else 0)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i) _
    (fun _ => by split_ifs <;> omega)

abbrev originalChoice (v : Fin (s + 1)) :=
  AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ HeckeExponents.neighborLevel i)
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) (p v) (Over.mk b)

def activeChoiceEquiv : originalChoice q c i p K b 0 ≃
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ HeckeExponents.neighborLevel i)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) (p 0) (Over.mk b) :=
  ChoiceTypeTransport.supportedChoiceTypeEquiv _ _ (by
    rw [HeckeExponents.neighborExponents_active]
    exact AddEquiv.refl _)

def compactChoiceEquiv (v : Fin s) : originalChoice q c i p K b v.succ ≃
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ HeckeExponents.neighborLevel i)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if c v then HeckeExponents.neighborLevel i else 0))
      (p v.succ) (Over.mk b) :=
  ChoiceTypeTransport.supportedChoiceTypeEquiv _ _ (by
    rw [HeckeExponents.neighborExponents_compact 0 v.succ (Fin.succ_ne_zero v)]
    exact AddEquiv.refl _)

variable (coordinates : ∀ v : Fin s,
  Additive (Over.mk b ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v.succ)) ≃+
    (Fin 3 → ZMod (q ^ HeckeExponents.neighborLevel i)))

def originalCompactChoice (v : Fin s) : originalChoice q c i p K b v.succ :=
  (compactChoiceEquiv q c i p K b v).symm
    (CompactChoices.geometricCompactChoice q (HeckeExponents.neighborLevel i) (c v) K b (p v.succ) (coordinates v))

theorem originalCompactChoice_unique (v : Fin s) (F : originalChoice q c i p K b v.succ) :
    F = originalCompactChoice q c i p K b coordinates v := by
  apply (compactChoiceEquiv q c i p K b v).injective
  rw [originalCompactChoice, Equiv.apply_symm_apply]
  exact CompactChoices.geometricCompactChoice_unique q (HeckeExponents.neighborLevel i) (c v) K b (p v.succ) (coordinates v) _

def originalTupleSubspaceEquiv : (∀ v, originalChoice q c i p K b v) ≃
    {L : Submodule (ZMod q)
      (ActiveTorsionChoices.killedSubgroup q (Additive (Over.mk b ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p 0)))) //
      Module.finrank (ZMod q) L = HeckeExponents.neighborLevel i} :=
  (zeroComponentEquiv (originalChoice q c i p K b)
    (originalCompactChoice q c i p K b coordinates)
    (originalCompactChoice_unique q c i p K b coordinates)).trans
      ((activeChoiceEquiv q c i p K b).trans
        (ActiveChoices.geometricActiveChoiceEquiv q (HeckeExponents.neighborLevel i) i K b (p 0)))

theorem originalTupleSubspaceEquiv_membership
    (F : ∀ v, originalChoice q c i p K b v)
    (x : ActiveTorsionChoices.killedSubgroup q (Additive (Over.mk b ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p 0)))) :
    x ∈ (originalTupleSubspaceEquiv q c i p K b coordinates F).val ↔
      x.val.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ HeckeExponents.neighborLevel i) (p 0) ∈
        (F 0).val.subgroup.points (Over.mk b) (𝟙 _) :=
  ActiveChoices.geometricActiveChoiceEquiv_membership q (HeckeExponents.neighborLevel i) i K b (p 0)
    (activeChoiceEquiv q c i p K b (F 0)) x

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.Enumeration.Neighbor
