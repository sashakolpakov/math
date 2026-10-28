import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalCoefficientFrameNeighborhood
import Mathlib.Order.ULift

/-! # Pointed Finite Affine Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.PointedFiniteAffineCover.LocalPointedFiniteAffineCover

noncomputable section

/-! A finite ordered affine cover with one member containing the image
of a morphism from an affine scheme with local coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {S X : Scheme.{u}}

structure Data (s : S ⟶ X) where
  I : Type u
  fintype : Fintype I
  linearOrder : LinearOrder I
  opens : I → X.Opens
  affine : ∀ i, IsAffineOpen (opens i)
  covers : iSup opens = ⊤
  distinguished : I
  point_in : ⊤ ≤ s ⁻¹ᵁ opens distinguished

/-- Compactness supplies the finite affine cover. The member containing
the coefficient-residue point contains the entire image of the local base. -/
theorem nonempty [IsAffine S] [IsLocalRing Γ(S, ⊤)] [CompactSpace X]
    (s : S ⟶ X) : Nonempty (Data s) := by
  classical
  have ha (x : X) : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  choose U hUa hxU using ha
  have hcover : Set.univ ⊆ ⋃ x : X, (U x : Set X) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (U x : Set X))
    (fun x => (U x).isOpen) hcover
  let e := (Fintype.equivFin t).symm
  let V : ULift.{u} (Fin (Fintype.card t)) → X.Opens := fun i => U (e i.down).1
  have hV : iSup V = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
    obtain ⟨hit, hxi⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨⟨e.symm ⟨i, hit⟩⟩, ?_⟩
    change x ∈ U (e (e.symm ⟨i, hit⟩)).1
    rw [e.apply_symm_apply]
    change x ∈ (U i : Set X)
    exact hxi
  let x₀ := ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S
    (IsLocalRing.ResidueField Γ(S, ⊤))
    (IsLocalRing.closedPoint (IsLocalRing.ResidueField Γ(S, ⊤)))
  have hx₀ : s x₀ ∈ iSup V := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx₀
  refine ⟨⟨ULift.{u} (Fin (Fintype.card t)), inferInstance, inferInstance,
    V, (fun j => hUa (e j.down).1), hV, i, ?_⟩⟩
  exact (Quotients.FiniteDescent.LocalCoefficientFrameNeighborhood.Construction.ModelFrameNeighborhood.coefficientResidue_open_eq_top
    S (s ⁻¹ᵁ V i) hi).ge

/-- A finite ordered affine cover with a member containing the full local-base image. -/
def ofLocalBase [IsAffine S] [IsLocalRing Γ(S, ⊤)] [CompactSpace X]
    (s : S ⟶ X) : Data s :=
  (nonempty s).some

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.PointedFiniteAffineCover.LocalPointedFiniteAffineCover
