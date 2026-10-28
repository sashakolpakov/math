import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoefficientBaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Relations Base Change Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RelationsBaseChangeMap.GradedHilbert

noncomputable section

/-! The tensor map onto base-changed homogeneous ideal relations is always surjective. -/

open _root_.MvPolynomial TensorProduct

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ)

def degreeRelationsBaseChangeMap : S ⊗[R] Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d →ₗ[R]
    Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d :=
  (((Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (R := R) (S := S) (n := n) d).restrictScalars R).toLinearMap.comp
    ((Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).subtype.lTensor S)).codRestrict ((Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d).restrictScalars R) (by
      intro x
      let p := Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d
      let q := Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d
      apply (Submodule.Quotient.mk_eq_zero q).mp
      change q.mkQ (Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (S := S) d (p.subtype.lTensor S x)) = 0
      rw [← Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv_quotient]
      have hz : p.mkQ.comp p.subtype = 0 := (LinearMap.exact_subtype_mkQ p).linearMap_comp_eq_zero
      rw [← LinearMap.lTensor_comp_apply, hz, LinearMap.lTensor_zero, LinearMap.zero_apply, LinearEquiv.map_zero])

theorem degreeRelationsBaseChangeMap_val (x : S ⊗[R] Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d) :
    (degreeRelationsBaseChangeMap (S := S) I d x).val =
      Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (S := S) d (((Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).subtype.lTensor S) x) := rfl

theorem degreeRelationsBaseChangeMap_tmul (s : S) (f : Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d) :
    (degreeRelationsBaseChangeMap (S := S) I d (s ⊗ₜ[R] f)).val.val =
      s • MvPolynomial.map (algebraMap R S) f.val.val :=
  Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv_tmul d s f.val

theorem degreeRelationsBaseChangeMap_surjective : Function.Surjective (degreeRelationsBaseChangeMap (S := S) I d) := by
  let p := Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d
  let q := Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d
  intro f
  obtain ⟨x, hx⟩ := (Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (R := R) (S := S) (n := n) d).surjective f.val
  have hz : p.mkQ.lTensor S x = 0 := by
    apply (Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := S) I d).injective
    rw [Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv_quotient, hx, LinearEquiv.map_zero]
    exact (Submodule.Quotient.mk_eq_zero q).mpr f.property
  have hz' : x ∈ (p.subtype.lTensor S).range := (le_of_eq (lTensor_mkQ S p)) hz
  obtain ⟨y, hy⟩ := hz'
  refine ⟨y, Subtype.ext ?_⟩
  rw [degreeRelationsBaseChangeMap_val, hy, hx]

theorem degreeRelations_baseChange_map :
    ((Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).baseChange S).map
      (Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (R := R) (S := S) (n := n) d).toLinearMap =
        Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d := by
  let p := Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := p.toBaseChange_surjective' S hx
    have hm := (degreeRelationsBaseChangeMap (S := S) I d y).property
    change Homogeneous.CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (S := S) d (p.subtype.lTensor S y) ∈ _ at hm
    change p.subtype.lTensor S y = x at hy
    rwa [hy] at hm
  · intro f hf
    obtain ⟨y, hy⟩ := degreeRelationsBaseChangeMap_surjective (S := S) I d ⟨f, hf⟩
    exact ⟨p.subtype.lTensor S y, (p.toBaseChange S y).property, congrArg Subtype.val hy⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RelationsBaseChangeMap.GradedHilbert
