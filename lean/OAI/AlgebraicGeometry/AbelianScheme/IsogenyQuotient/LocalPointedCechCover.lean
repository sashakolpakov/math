import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointedFiniteCechCover
import Mathlib.AlgebraicGeometry.Stalk

/-! # Local Pointed Cech Cover -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalPointedCechCover.Construction

noncomputable section

/-! Over a local base, an affine chart containing the section's
closed point contains its entire image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem exists_local_pointed_finite_cech_cover
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} [CompactSpace X] (σ : Spec (.of R) ⟶ X) :
    ∃ (I : Type u) (_ : Fintype I) (_ : LinearOrder I) (U : I → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ ∧
      ∃ a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex I 0, ⊤ ≤ σ ⁻¹ᵁ (∏ᶜ fun k : Fin 1 => U (a.val k)) := by
  classical
  let C := X.affineCover.finiteSubcover
  let J := C.I₀
  let I := ULift.{u} (Fin (Fintype.card J))
  let e : I ≃ J := Equiv.ulift.trans (Fintype.equivFin J).symm
  let U (i : I) : X.Opens := (C.f (e i)).opensRange
  have hUa (i : I) : IsAffineOpen (U i) := by
    have : IsAffine (C.X (e i)) := by change IsAffine (Spec _); infer_instance
    exact isAffineOpen_opensRange (C.f (e i))
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨j, y, hy⟩ := C.exists_eq x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨e.symm j, by
      change x ∈ (C.f (e (e.symm j))).opensRange
      rw [e.apply_symm_apply]
      exact ⟨y, hy⟩⟩
  have ht : σ (IsLocalRing.closedPoint R) ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
  let a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex I 0 := ⟨fun _ => i, by
    intro j k hjk
    have hj : j.val < 1 := j.isLt
    have hk : k.val < 1 := k.isLt
    exact False.elim (hjk.ne (Fin.ext (by omega)))⟩
  refine ⟨I, inferInstance, inferInstance, U, hUa, hU, a, ?_⟩
  apply (Scheme.preimage_eq_top_of_closedPoint_mem σ ?_).ge
  change σ (IsLocalRing.closedPoint R) ∈ (∏ᶜ fun _ : Fin 1 => U i)
  rw [SheafCohomology.Cech.Cochains.TopologicalSpace.Opens.piObj_eq_iInf]
  simpa using hi

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalPointedCechCover.Construction
