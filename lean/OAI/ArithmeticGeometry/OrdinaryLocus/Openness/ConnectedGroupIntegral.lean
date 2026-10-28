import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatTranslations
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced
import Mathlib.Topology.Connected.Clopen

/-! # Connected Group Integral -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConnectedGroupIntegral.Construction

noncomputable section

/-! Irreducibility of connected algebraic groups for the Openness argument. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- In a connected Noetherian Jacobson scheme, transitivity on closed
points forces irreducibility. -/
theorem irreducibleSpace_of_transitive_closedPoints
    (X : Scheme) [NoetherianSpace X] [JacobsonSpace X] [ConnectedSpace X]
    (htrans : ∀ (x y : X), IsClosed {x} → IsClosed {y} →
      ∃ α : X ≅ X, α.hom x = y) : IrreducibleSpace X := by
  let x₀ : X := Classical.choice inferInstance
  let C := irreducibleComponent x₀
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x₀
  obtain ⟨U, hUopen, hUnonempty, hUC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  have hUirr : IsPreirreducible U := hC.1.2.open_subset hUopen hUC
  let I := {V : X.Opens // IsPreirreducible (V : Set X)}
  let V : I → X.Opens := Subtype.val
  have htop : iSup V = ⊤ := by
    by_contra hne
    have hex : ∃ x : X, x ∉ iSup V := by
      by_contra! h
      exact hne (le_antisymm le_top (fun x _ => h x))
    obtain ⟨x', hx'⟩ := hex
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints
      (Z := ((iSup V : X.Opens) : Set X)ᶜ) ⟨x', hx'⟩
      (iSup V).isOpen.isClosed_compl.isLocallyClosed
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hUnonempty hUopen.isLocallyClosed
    obtain ⟨α, hxy⟩ := htrans x y hxc hyc
    let W : X.Opens := α.hom ⁻¹ᵁ (⟨U, hUopen⟩ : X.Opens)
    have hWirr : IsPreirreducible (W : Set X) :=
      hUirr.preimage α.hom.isOpenEmbedding
    have hxW : x ∈ W := by change α.hom x ∈ U; rwa [hxy]
    exact hx ((le_iSup V ⟨W, hWirr⟩) hxW)
  have hlocal (x : X) : ∃ W : X.Opens, x ∈ W ∧ IsPreirreducible (W : Set X) := by
    have hx : x ∈ iSup V := by rw [htop]; trivial
    obtain ⟨W, hW⟩ := Opens.mem_iSup.mp hx
    exact ⟨W.val, hW, W.property⟩
  have hCopen : IsOpen C := by
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    obtain ⟨W, hxW, hWirr⟩ := hlocal x
    obtain ⟨D, hD, hWD⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (W : Set X) ⟨⟨x, hxW⟩, hWirr⟩
    have hCD : C ⊆ D :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 W.isOpen
        ⟨x, hx, hxW⟩).trans
        ((isClosed_of_mem_irreducibleComponents D hD).closure_subset_iff.mpr
          (Set.inter_subset_right.trans hWD))
    exact ⟨W, hWD.trans (hC.2 hD.1 hCD), W.isOpen, hxW⟩
  have hCeq : C = Set.univ :=
    IsClopen.eq_univ ⟨isClosed_of_mem_irreducibleComponents C hC, hCopen⟩ hC.1.nonempty
  apply (irreducibleSpace_def X).mpr
  change IsIrreducible (Set.univ : Set X)
  rw [← hCeq]
  exact hC.1

/-- A connected smooth proper commutative group over an algebraically
closed field is integral. -/
theorem isIntegral_connected_smooth_proper_group
    {K : Type*} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] : IsIntegral A.left := by
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := ⟨⟩
  have : IrreducibleSpace A.left := irreducibleSpace_of_transitive_closedPoints A.left
    (fun x y hx hy => by
      obtain ⟨α, _, hxy, _⟩ := FlatTranslations.Construction.multiplication_transitive_automorphisms A 1 x y hx hy
      exact ⟨α, hxy⟩)
  have : IsReduced A.left := SmoothReduced.Construction.isReduced_smooth_over_field A.hom
  exact isIntegral_of_irreducibleSpace_of_isReduced A.left

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConnectedGroupIntegral.Construction
