import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenerationAffinePointCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientClassification

/-! # Zero Relation Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroRelationLocus

noncomputable section

/-! Vanishing of the actual quotient relation module is represented by an open subset. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {S : Scheme.{u}} {M : Over S}

def grassmannZeroRelationOpen (q : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S) : M.left.Opens :=
  Grassmann.GenerationOpen.grassmannGenerationOpen q q (fun e : ULift.{u} Empty => nomatch e.down) (fun e => nomatch e.down)

theorem grassmannZeroRelationOpen_affine_point_iff
    (q : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
    (R : CommRingCat.{u}) (f : Spec R ⟶ S) (x : Over.mk f ⟶ M)
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
    (hN : x ≫ q = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N) :
    Set.range x.left ⊆ (grassmannZeroRelationOpen q : Set M.left) ↔ N.toSubmodule = ⊥ := by
  have h := GenerationAffinePointCriterion.grassmannGenerationOpen_affine_point_iff q q
    (fun e : ULift.{u} Empty => nomatch e.down) (fun e => nomatch e.down)
    R f x N N hN hN (fun e : ULift.{u} Empty => nomatch e.down) (fun e => nomatch e.down)
  simp only [iSup_of_empty] at h
  exact h

variable (σ : Type v) [Finite σ] (d r : ℕ)
variable {S' : Scheme.{max u v}} {M' : Over S'}
variable (q : M' ⟶ Homogeneous.QuotientParameters.homogeneousQuotientParameterScheme.{u, v} σ d r S')

def homogeneousZeroRelationOpen : M'.left.Opens := grassmannZeroRelationOpen q

theorem homogeneousZeroRelationOpen_affine_point_iff
    (R : CommRingCat.{max u v}) (f : Spec R ⟶ S') (x : Over.mk f ⟶ M')
    (N : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R d) r)
    (hN : x ≫ q = Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d r R f N) :
    Set.range x.left ⊆ (homogeneousZeroRelationOpen σ d r q : Set M'.left) ↔ N.toSubmodule = ⊥ := by
  have h := grassmannZeroRelationOpen_affine_point_iff q R f x
    (Homogeneous.QuotientClassification.homogeneousLiftedQuotient.{u, v} σ d r R N)
    (hN.trans (Homogeneous.QuotientClassification.homogeneousQuotientAffinePointEquiv_coordinates σ d r R f N))
  rw [Homogeneous.QuotientClassification.homogeneousLiftedQuotient_relations] at h
  refine h.trans ?_
  constructor
  · intro hz
    apply Submodule.map_injective_of_injective (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, v} σ d R).injective
    rw [Submodule.map_bot]
    exact hz
  · intro hz
    rw [hz, Submodule.map_bot]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroRelationLocus
