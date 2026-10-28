import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.OppositeComparison

/-! # Projective Basic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveBasic.CochainComplex

open _root_.CochainComplex

/-!
# K-projective cochain complexes

We define the notion of K-projective cochain complex in an abelian category,
and show that bounded above complexes of projective objects are K-projective.

## TODO (@joelriou)
* Provide an API for computing `Ext`-groups using a projective resolution

## References
* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein1998]

-/

/- HilbertConstruction-local adaptation, using default elaboration settings. -/

open _root_.CategoryTheory Limits Preadditive Opposite

variable {C : Type*} [Category* C] [Abelian C]

-- TODO (@joelriou): show that this definition is equivalent to the
-- original definition by Spaltenstein saying that whenever `L`
-- is acyclic, then `HomComplex K L` is acyclic. (The condition below
-- is equivalent to the acyclicity of `HomComplex K L` in degree
-- `0`, and the general case follows by shifting `L`.)
/-- A cochain complex `K` is K-projective if any morphism `K ⟶ L`
with `L` acyclic is homotopic to zero. -/
class IsKProjective (K : CochainComplex C ℤ) : Prop where
  nonempty_homotopy_zero {L : CochainComplex C ℤ} (f : K ⟶ L) :
    L.Acyclic → Nonempty (Homotopy f 0)

/-- A choice of homotopy to zero for a morphism from a
K-projective cochain complex to an acyclic cochain complex. -/
noncomputable irreducible_def IsKProjective.homotopyZero
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hL : L.Acyclic) [IsKProjective K] :
    Homotopy f 0 :=
  (IsKProjective.nonempty_homotopy_zero f hL).some

lemma isKProjective_iff_leftOrthogonal (K : CochainComplex C ℤ) :
    IsKProjective K ↔
      (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  refine ⟨fun _ L f hL ↦ ?_,
      fun hK ↦ ⟨fun {L} f hL ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKProjective.homotopyZero f hL), Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [hK ((HomotopyCategory.quotient _ _).map f) hL, Functor.map_zero]

lemma IsKProjective.leftOrthogonal (K : CochainComplex C ℤ) [IsKProjective K] :
    (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  rwa [← isKProjective_iff_leftOrthogonal]

lemma isKProjective_of_op {K : CochainComplex C ℤ}
    (hK : IsKInjective ((Cochain.OppositeComparison.CochainComplex.opEquivalence C).functor.obj (op K))) :
    IsKProjective K where
  nonempty_homotopy_zero {L} f hL :=
    ⟨Cochain.OppositeComparison.CochainComplex.homotopyUnop ((IsKInjective.homotopyZero
      ((Cochain.OppositeComparison.CochainComplex.opEquivalence C).functor.map f.op) (Cochain.OppositeComparison.CochainComplex.acyclic_op hL)).trans
        (.ofEq (by simp)))⟩

attribute [local simp] Cochain.OppositeComparison.CochainComplex.opEquivalence Cochain.OppositeComparison.ChainComplex.cochainComplexEquivalence in
open _root_.CochainComplex.HomComplex.Cochain.InductionUp in
lemma isKProjective_of_projective (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ (n : ℤ), Projective (K.X n)] :
    IsKProjective K := by
  let L := ((Cochain.OppositeComparison.CochainComplex.opEquivalence C).functor.obj (op K))
  have (n : ℤ) : Injective (L.X n) := by
    change Injective (op (K.X (-n)))
    infer_instance
  have : L.IsStrictlyGE (-d) := by
    rw [isStrictlyGE_iff]
    intro i hi
    change IsZero (op (K.X (-i)))
    exact (K.isZero_of_isStrictlyLE d (-i) (by omega)).op
  exact isKProjective_of_op (isKInjective_of_injective L (-d))

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveBasic.CochainComplex
