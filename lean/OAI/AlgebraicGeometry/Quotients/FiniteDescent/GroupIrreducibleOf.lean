import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Connected.Clopen

/-! # Group Irreducible Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupIrreducibleOf.Construction.GroupIrreducible

/-! # Irreducibility of connected groups over an algebraically closed field -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

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

theorem irreducibleSpace_of_connected_group
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [GeometricallyConnected A.hom] : IrreducibleSpace A.left := by
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := ⟨⟩
  apply irreducibleSpace_of_transitive_closedPoints A.left
  intro x y hx hy
  let x' : 𝟙_ (Over (Spec (.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom x hx) (pointOfClosedPoint_comp A.hom x hx)
  let y' : 𝟙_ (Over (Spec (.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom y hy) (pointOfClosedPoint_comp A.hom y hy)
  let b := x'⁻¹ * y'
  let α : A.left ≅ A.left := GroupAffine.Construction.GroupAffineNeighborhood.translate A b
  have hxy : x' ≫ (GrpObj.mulRight b).hom = y' := by
    change x' ≫ (𝟙 A * (toUnit A ≫ b)) = y'
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      comp_toUnit, toUnit_unit, Category.id_comp]
    exact mul_inv_cancel_left x' y'
  refine ⟨α, ?_⟩
  have he : α.hom (x'.left (IsLocalRing.closedPoint K)) = y'.left (IsLocalRing.closedPoint K) :=
    congrArg (fun f : Spec (.of K) ⟶ A.left => f (IsLocalRing.closedPoint K))
      (congrArg Over.Hom.left hxy)
  have hx' : x'.left (IsLocalRing.closedPoint K) = x := pointOfClosedPoint_apply A.hom x hx _
  have hy' : y'.left (IsLocalRing.closedPoint K) = y := pointOfClosedPoint_apply A.hom y hy _
  rw [hx', hy'] at he
  exact he

theorem exists_affineOpen_of_finite
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [GeometricallyConnected A.hom]
    (F : Set A.left) (hF : F.Finite) :
    ∃ U : A.left.Opens, IsAffineOpen U ∧ F ⊆ U := by
  have : IrreducibleSpace A.left := irreducibleSpace_of_connected_group A
  exact GroupAffine.Construction.GroupAffineNeighborhood.exists_affineOpen_of_finite A F hF

/-- Irreducibility descends from the algebraic closure of an arbitrary
base field, using the surjective projection of the base change. -/
theorem irreducibleSpace_over_field
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [GeometricallyConnected A.hom] : IrreducibleSpace A.left := by
  let f : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  let B := (Over.pullback f).obj A
  let : GrpObj B := Functor.grpObjObj
  have : IsCommMonObj B := inferInstanceAs (IsCommMonObj ((Over.pullback f).obj A))
  have : IsProper B.hom := by dsimp [B]; infer_instance
  have : GeometricallyConnected B.hom := by dsimp [B]; infer_instance
  have : IrreducibleSpace (Limits.pullback A.hom f : Scheme.{u}) :=
    irreducibleSpace_of_connected_group B
  have : Surjective f := ⟨fun _ => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  exact (Limits.pullback.fst A.hom f).surjective.irreducibleSpace
    (Limits.pullback.fst A.hom f).continuous

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupIrreducibleOf.Construction.GroupIrreducible
