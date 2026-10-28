import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.Neighbors

/-! # Generic Parameters -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericParameters

noncomputable section

/-!
The generic enumeration bridge for a split block. The inputs are coordinate
equivalences on the actual generic points of M, E, and H_U, together with
the coordinate formulas for the supplied morphisms e_U and chi_f. No
subgroup enumeration, fiber count, or quotient-target equation is assumed.
The proof computes each graph/product image and obtains every subspace
exactly once from the previously proved classification.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]
variable {S : Scheme.{u}} {G M E : Over S}

/-- Generic coordinates of the actual product scheme, constructed from its
universal property and the chosen coordinates of its two factors. -/
def blockCoordinates (m : (G ⟶ M) ≃ F) (v : (G ⟶ E) ≃ V) :
    (G ⟶ M ⊗ E) ≃ V × F where
  toFun a := (v (a ≫ snd M E), m (a ≫ fst M E))
  invFun a := lift (m.symm a.2) (v.symm a.1)
  left_inv a := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  right_inv a := by simp

variable (H : Submodule F V → Over S) (e : ∀ U, H U ⟶ E)
variable (χ : ∀ U : Submodule F V, (U →ₗ[F] F) → (H U ⟶ M))
variable (m : (G ⟶ M) ≃ F) (v : (G ⟶ E) ≃ V)
variable (h : ∀ U : Submodule F V, (G ⟶ H U) ≃ U)
variable (he : ∀ (U : Submodule F V) (a : G ⟶ H U), v (a ≫ e U) = (h U a).val)
variable (hχ : ∀ (U : Submodule F V) (l : U →ₗ[F] F) (a : G ⟶ H U),
  m (a ≫ χ U l) = l (h U a))

def kernelPointImage (K : Intrinsic.Neighbors.KernelPresentation (M ⊗ E)) : Set (V × F) :=
  Set.range (fun a : G ⟶ K.carrier => blockCoordinates m v (a ≫ K.inclusion))

include he hχ in
lemma graph_point_coordinates (U : Submodule F V) (l : U →ₗ[F] F) (a : G ⟶ H U) :
    blockCoordinates m v (a ≫ QuotientGraphs.graphKernel (𝟙 (M ⊗ E)) (e U) (χ U l)) =
      ((h U a).val, l (h U a)) := by
  change (v ((a ≫ (lift (χ U l) (e U) ≫ 𝟙 _)) ≫ snd M E),
    m ((a ≫ (lift (χ U l) (e U) ≫ 𝟙 _)) ≫ fst M E)) = _
  simp only [Category.comp_id, Category.assoc, lift_snd, lift_fst]
  exact Prod.ext (he U a) (hχ U l a)

include h he hχ in
theorem generic_graph_image (U : Submodule F V) (l : U →ₗ[F] F) :
    kernelPointImage m v ⟨H U, QuotientGraphs.graphKernel (𝟙 (M ⊗ E)) (e U) (χ U l)⟩ =
      (SubspaceCounts.Construction.fiberGraph U l : Set (V × F)) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    change blockCoordinates m v (a ≫ QuotientGraphs.graphKernel (𝟙 (M ⊗ E)) (e U) (χ U l)) ∈
      SubspaceCounts.Construction.fiberGraph U l
    rw [graph_point_coordinates H e χ m v h he hχ U l a]
    exact ⟨h U a, rfl⟩
  · rintro ⟨a, ha⟩
    refine ⟨(h U).symm a, ?_⟩
    change blockCoordinates m v ((h U).symm a ≫
      QuotientGraphs.graphKernel (𝟙 (M ⊗ E)) (e U) (χ U l)) = z
    rw [graph_point_coordinates H e χ m v h he hχ U l ((h U).symm a),
      Equiv.apply_symm_apply]
    exact ha

include he in
lemma mixed_point_coordinates (U : Submodule F V) (a : G ⟶ M ⊗ H U) :
    blockCoordinates m v (a ≫ QuotientGraphs.mixedKernel (𝟙 (M ⊗ E)) (e U)) =
      ((h U (a ≫ snd M (H U))).val, m (a ≫ fst M (H U))) := by
  change (v ((a ≫ ((𝟙 M ⊗ₘ e U) ≫ 𝟙 _)) ≫ snd M E),
    m ((a ≫ ((𝟙 M ⊗ₘ e U) ≫ 𝟙 _)) ≫ fst M E)) = _
  simp only [Category.comp_id, Category.assoc, tensorHom_snd, tensorHom_fst]
  exact Prod.ext (he U (a ≫ snd M (H U))) rfl

include h he in
theorem generic_mixed_image (U : Submodule F V) :
    kernelPointImage m v ⟨M ⊗ H U, QuotientGraphs.mixedKernel (𝟙 (M ⊗ E)) (e U)⟩ =
      (U.comap (LinearMap.fst F V F) : Set (V × F)) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    change blockCoordinates m v (a ≫ QuotientGraphs.mixedKernel (𝟙 (M ⊗ E)) (e U)) ∈
      U.comap (LinearMap.fst F V F)
    rw [mixed_point_coordinates H e m v h he U a]
    exact (h U (a ≫ snd M (H U))).property
  · intro hz
    let a : G ⟶ M ⊗ H U := lift (m.symm z.2) ((h U).symm ⟨z.1, hz⟩)
    refine ⟨a, ?_⟩
    change blockCoordinates m v (a ≫ QuotientGraphs.mixedKernel (𝟙 (M ⊗ E)) (e U)) = z
    rw [mixed_point_coordinates H e m v h he U a]
    simp only [a, lift_snd, lift_fst, Equiv.apply_symm_apply]

include h he hχ in
/-- Every constructed generic kernel has exactly the indexed subspace as
its image. The coordinate formulas prove the enumeration identity. -/
theorem generic_subspace_kernel_image (L : Submodule F (V × F)) :
    kernelPointImage m v (Intrinsic.Neighbors.subspaceKernel H (𝟙 (M ⊗ E)) e χ L) =
      (L : Set (V × F)) := by
  obtain ⟨⟨U, L | L⟩, rfl⟩ := (SubspaceCounts.Construction.allSubspacesEquiv (F := F) (V := V)).surjective L
  · rw [Intrinsic.Neighbors.subspaceKernel_equiv]
    change kernelPointImage m v
      ⟨H U, QuotientGraphs.graphKernel (𝟙 (M ⊗ E)) (e U) (χ U ((SubspaceCounts.Construction.disjointLiftEquiv U).symm L))⟩ =
        (L.val : Set (V × F))
    rw [generic_graph_image H e χ m v h he hχ]
    have hgraph := congrArg Subtype.val ((SubspaceCounts.Construction.disjointLiftEquiv U).apply_symm_apply L)
    exact congrArg (fun K : Submodule F (V × F) => (K : Set (V × F))) hgraph
  · rw [Intrinsic.Neighbors.subspaceKernel_equiv]
    change kernelPointImage m v ⟨M ⊗ H U, QuotientGraphs.mixedKernel (𝟙 (M ⊗ E)) (e U)⟩ =
      (L.val : Set (V × F))
    rw [generic_mixed_image H e m v h he]
    exact congrArg (fun K : Submodule F (V × F) => (K : Set (V × F)))
      (SubspaceCounts.Construction.containingLift_eq_preimage U L).symm

include h he hχ in
theorem generic_subspace_kernel_image_injective :
    Function.Injective (fun L : Submodule F (V × F) =>
      kernelPointImage m v (Intrinsic.Neighbors.subspaceKernel H (𝟙 (M ⊗ E)) e χ L)) := by
  intro L₁ L₂ hsame
  change kernelPointImage m v (Intrinsic.Neighbors.subspaceKernel H (𝟙 (M ⊗ E)) e χ L₁) =
    kernelPointImage m v (Intrinsic.Neighbors.subspaceKernel H (𝟙 (M ⊗ E)) e χ L₂) at hsame
  rw [generic_subspace_kernel_image H e χ m v h he hχ,
    generic_subspace_kernel_image H e χ m v h he hχ] at hsame
  exact SetLike.coe_injective hsame

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericParameters
