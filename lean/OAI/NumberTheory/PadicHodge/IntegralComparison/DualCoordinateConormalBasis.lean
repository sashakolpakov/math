import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalRank
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Dual Coordinate Conormal Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DualCoordinateConormalBasis

noncomputable section

/-! Actual generators with dual derivations give a basis of the conormal
module. No characteristic assumption or regularity assertion is needed. -/

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (I : Ideal R)

def derivationOnIdeal (D : Derivation k R R) : I →ₗ[R] R ⧸ I where
  toFun x := Ideal.Quotient.mk I (D x.val)
  map_add' x y := by simp
  map_smul' a x := by
    change Ideal.Quotient.mk I (D (a * x.val)) = a • Ideal.Quotient.mk I (D x.val)
    rw [Derivation.leibniz, map_add]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, Algebra.smul_def]

def functional (D : Derivation k R R) : I.Cotangent →ₗ[R ⧸ I] R ⧸ I :=
  (Ideal.Cotangent.lift (derivationOnIdeal I D) (by
    intro x y
    change Ideal.Quotient.mk I (D (x.val * y.val)) = 0
    rw [Derivation.leibniz, map_add]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr x.property,
      Ideal.Quotient.eq_zero_iff_mem.mpr y.property])).extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective

theorem functional_apply (D : Derivation k R R) (x : I) :
    functional I D (I.toCotangent x) = Ideal.Quotient.mk I (D x.val) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (z : ι → I) (D : ι → Derivation k R R)
  (hD : ∀ i j, D i (z j).val = if i = j then 1 else 0)
  (hgen : Ideal.span (Set.range (fun i => (z i).val)) = I)

include hD in
theorem independent : LinearIndependent (R ⧸ I) (fun i => I.toCotangent (z i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have h := congrArg (functional I (D i)) ha
  simpa [map_sum, map_smul, functional_apply, hD, Finset.sum_ite_eq] using h

include hgen in
omit [Fintype ι] [DecidableEq ι] in
theorem spans : Submodule.span (R ⧸ I) (Set.range (fun i => I.toCotangent (z i))) = ⊤ := by
  apply Submodule.span_eq_top_of_span_eq_top R (R ⧸ I)
  have hz : Submodule.span R (Set.range z) = ⊤ := by
    apply (Submodule.map_injective_of_injective I.subtype_injective)
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    exact hgen
  have h := congrArg (Submodule.map I.toCotangent) hz
  simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    LinearMap.range_eq_top.mpr I.toCotangent_surjective, Function.comp_def] using h

def basis : Module.Basis ι (R ⧸ I) I.Cotangent :=
  Module.Basis.mk (independent I z D hD) (by rw [spans I z hgen])

theorem basis_apply (i : ι) : basis I z D hD hgen i = I.toCotangent (z i) :=
  Module.Basis.mk_apply _ _ i

theorem coord_eq_functional (i : ι) :
    (basis I z D hD hgen).coord i = functional I (D i) := by
  apply (basis I z D hD hgen).ext
  intro j
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  simp only [Finsupp.single_apply, basis_apply, functional_apply, hD]
  split_ifs <;> simp_all

theorem repr_toCotangent (x : I) (i : ι) :
    (basis I z D hD hgen).repr (I.toCotangent x) i =
      Ideal.Quotient.mk I (D i x.val) := by
  change (basis I z D hD hgen).coord i (I.toCotangent x) = _
  rw [coord_eq_functional, functional_apply]

include hD hgen in
theorem rankAtStalk (p : PrimeSpectrum (R ⧸ I)) :
    Module.rankAtStalk I.Cotangent p = Fintype.card ι := by
  let : Nontrivial (R ⧸ I) := p.nontrivial
  let : Module.Free (R ⧸ I) I.Cotangent := Module.Free.of_basis (basis I z D hD hgen)
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis (basis I z D hD hgen)]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DualCoordinateConormalBasis
