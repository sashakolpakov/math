import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.DeterminantCoordinates

/-! # Discriminant -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Discriminant

noncomputable section

/-! A single product of actual determinants cuts out the projective-frame
locus over every commutative ring, including nonreduced coefficient rings. -/
open scoped BigOperators Classical
universe u v w
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {κ : Type w} [Fintype κ]

def projectiveFrameDiscriminant (e : Module.Basis κ R V) (b : κ → V) (v : V) : R :=
  e.det b * ∏ i, e.det (Function.update b i v)

theorem projectiveFrameDiscriminant_basis (e b : Module.Basis κ R V) (v : V) :
    projectiveFrameDiscriminant e b v =
      (e.det b) ^ (Fintype.card κ + 1) * ∏ i, b.repr v i := by
  simp only [projectiveFrameDiscriminant, DeterminantCoordinates.basis_det_update_coordinate,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [pow_succ]
  ring

theorem projectiveFrameDiscriminant_isUnit_iff
    (e : Module.Basis κ R V) (b : κ → V) (v : V) :
    IsUnit (projectiveFrameDiscriminant e b v) ↔
      ∃ c : Module.Basis κ R V, (∀ i, c i = b i) ∧ ∀ i, IsUnit (c.repr v i) := by
  constructor
  · intro h
    have hd := (IsUnit.mul_iff.mp h).1
    have hm := IsUnit.prod_iff.mp (IsUnit.mul_iff.mp h).2
    obtain ⟨hli, hsp⟩ := (e.is_basis_iff_det).mpr hd
    let c := Module.Basis.mk hli hsp.ge
    have hc : (c : κ → V) = b := Module.Basis.coe_mk hli hsp.ge
    refine ⟨c, fun i => congrFun hc i, fun i => ?_⟩
    have hi := hm i (Finset.mem_univ i)
    rw [← hc, DeterminantCoordinates.basis_det_update_coordinate] at hi
    exact (IsUnit.mul_iff.mp hi).2
  · rintro ⟨c, hc, hu⟩
    have hcb : b = c := funext (fun i => (hc i).symm)
    rw [hcb, projectiveFrameDiscriminant_basis]
    exact ((e.isUnit_det c).pow _).mul (IsUnit.prod_iff.mpr (fun i _ => hu i))

theorem projectiveFrameDiscriminant_linearMap
    (e : Module.Basis κ R V) (b : κ → V) (v : V) (f : V →ₗ[R] V) :
    projectiveFrameDiscriminant e (f ∘ b) (f v) =
      f.det ^ (Fintype.card κ + 1) * projectiveFrameDiscriminant e b v := by
  have hm (i : κ) : Function.update (f ∘ b) i (f v) = f ∘ Function.update b i v := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simp [Function.update, hji]
  simp only [projectiveFrameDiscriminant, hm, Module.Basis.det_comp,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, pow_succ]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Discriminant
