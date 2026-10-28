import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod

/-! # Active Typed Subspaces -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces

noncomputable section

/-! The original active elementary group types are precisely the
subspaces of dimensions one, two, and three over the residue field.
The equivalence retains the underlying unmarked subgroup. -/

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents

variable (q : ℕ) [Fact q.Prime]

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

abbrev activeElementaryVectorSpace (i : Fin 3) :
    Module (ZMod q) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) :=
  AddCommGroup.zmodModule (HeckeExponents.activeElementaryModule_killed q i)

omit [Fact q.Prime] in
theorem activeElementary_card (i : Fin 3) :
    Nat.card (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) = q ^ HeckeExponents.neighborLevel i := by
  change Nat.card (ULift (∀ k : Fin 3, ZMod (q ^ HeckeExponents.activeExponents i k))) = _
  rw [Nat.card_ulift, Nat.card_pi]
  simp only [Nat.card_zmod]
  rw [Finset.prod_pow_eq_pow_sum, HeckeExponents.activeExponents_sum]

theorem activeElementary_finrank (i : Fin 3) :
    letI := activeElementaryVectorSpace q i
    Module.finrank (ZMod q) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) = HeckeExponents.neighborLevel i := by
  let := activeElementaryVectorSpace q i
  have : Module.Finite (ZMod q) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) := Module.Finite.of_finite
  apply Nat.pow_right_injective (Fact.out : q.Prime).two_le
  have h := Module.natCard_eq_pow_finrank (K := ZMod q) (V := AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i))
  rw [Nat.card_zmod] at h
  exact h.symm.trans (activeElementary_card q i)

def zmodLinearEquiv {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod q) V] [Module (ZMod q) W] (e : V ≃+ W) : V ≃ₗ[ZMod q] W :=
  { e with map_smul' := fun a x => ZMod.map_smul e a x }

variable (V : Type) [AddCommGroup V] [Module (ZMod q) V] [Finite V]

theorem active_type_iff_finrank (i : Fin 3) (J : AddSubgroup V) :
    Nonempty (J ≃+ AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) ↔
      Module.finrank (ZMod q) (AddSubgroup.toZModSubmodule q J) = HeckeExponents.neighborLevel i := by
  let := activeElementaryVectorSpace q i
  let : Module (ZMod q) J := inferInstanceAs (Module (ZMod q) (AddSubgroup.toZModSubmodule q J))
  have : Module.Finite (ZMod q) J := Module.Finite.of_finite
  have : Module.Finite (ZMod q) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i)) := Module.Finite.of_finite
  constructor
  · rintro ⟨e⟩
    exact (zmodLinearEquiv q e).finrank_eq.trans (activeElementary_finrank q i)
  · intro h
    obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (h.trans (activeElementary_finrank q i).symm)
    exact ⟨e.toAddEquiv⟩

def activeTypedSubspaceEquiv (i : Fin 3) :
    {J : AddSubgroup V // Nonempty (J ≃+ AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i))} ≃
      {L : Submodule (ZMod q) V // Module.finrank (ZMod q) L = HeckeExponents.neighborLevel i} :=
  (AddSubgroup.toZModSubmodule q).toEquiv.subtypeEquiv (active_type_iff_finrank q V i)

theorem activeTypedSubspaceEquiv_membership (i : Fin 3)
    (J : {J : AddSubgroup V // Nonempty (J ≃+ AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i))})
    (x : V) : x ∈ (activeTypedSubspaceEquiv q V i J).val ↔ x ∈ J.val := Iff.rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces
