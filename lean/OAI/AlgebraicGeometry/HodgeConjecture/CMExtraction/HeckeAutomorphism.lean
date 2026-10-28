import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Hecke Automorphism -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphism.Local

noncomputable section

section

/-! A group automorphism preserving the actual compact subgroup transports
the spherical algebra by its permutation of right cosets. -/

open scoped Classical

variable {G : Type*} [Group G] (K : Subgroup G) (a : G ≃* G)
  (ha : ∀ g, a g ∈ K ↔ g ∈ K)

include ha in
def cosetAutomorphism : G ⧸ K ≃ G ⧸ K :=
  Quotient.congr a.toEquiv (by
    intro g h
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    change g⁻¹ * h ∈ K ↔ (a g)⁻¹ * a h ∈ K
    rw [← map_inv, ← map_mul, ha])

theorem cosetAutomorphism_mk (g : G) :
    cosetAutomorphism K a ha (QuotientGroup.mk g) = QuotientGroup.mk (a g) := rfl

theorem cosetAutomorphism_smul (g : G) (x : G ⧸ K) :
    cosetAutomorphism K a ha (g • x) = a g • cosetAutomorphism K a ha x := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  change QuotientGroup.mk (a (g * h)) = QuotientGroup.mk (a g * a h)
  rw [map_mul]

def cosetModuleAutomorphism : AbelianScheme.TateComparison.HeckeKernel.CosetModule K ≃ₗ[ℚ] AbelianScheme.TateComparison.HeckeKernel.CosetModule K :=
  Finsupp.domLCongr (cosetAutomorphism K a ha)

theorem cosetModuleAutomorphism_single (x : G ⧸ K) (r : ℚ) :
    cosetModuleAutomorphism K a ha (Finsupp.single x r) =
      Finsupp.single (cosetAutomorphism K a ha x) r := Finsupp.domLCongr_single _ _ _

theorem cosetModuleAutomorphism_translate (g : G) (v : AbelianScheme.TateComparison.HeckeKernel.CosetModule K) :
    cosetModuleAutomorphism K a ha (AbelianScheme.TateComparison.HeckeKernel.translate K g v) =
      AbelianScheme.TateComparison.HeckeKernel.translate K (a g) (cosetModuleAutomorphism K a ha v) := by
  have h : (cosetModuleAutomorphism K a ha).toLinearMap.comp (AbelianScheme.TateComparison.HeckeKernel.translate K g) =
      (AbelianScheme.TateComparison.HeckeKernel.translate K (a g)).comp (cosetModuleAutomorphism K a ha).toLinearMap := by
    apply Finsupp.lhom_ext
    intro x r
    change cosetModuleAutomorphism K a ha (AbelianScheme.TateComparison.HeckeKernel.translate K g (Finsupp.single x r)) = _
    rw [AbelianScheme.TateComparison.HeckeKernel.translate_single, cosetModuleAutomorphism_single]
    change _ = AbelianScheme.TateComparison.HeckeKernel.translate K (a g) (cosetModuleAutomorphism K a ha (Finsupp.single x r))
    rw [cosetModuleAutomorphism_single, AbelianScheme.TateComparison.HeckeKernel.translate_single, cosetAutomorphism_smul]
  exact LinearMap.congr_fun h v

theorem cosetConjugation_translate (g : G) :
    (cosetModuleAutomorphism K a ha).conjAlgEquiv ℚ (AbelianScheme.TateComparison.HeckeKernel.translate K g) = AbelianScheme.TateComparison.HeckeKernel.translate K (a g) := by
  apply LinearMap.ext
  intro v
  change cosetModuleAutomorphism K a ha
    (AbelianScheme.TateComparison.HeckeKernel.translate K g ((cosetModuleAutomorphism K a ha).symm v)) = _
  rw [cosetModuleAutomorphism_translate, LinearEquiv.apply_symm_apply]

theorem cosetConjugation_spherical (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) :
    (cosetModuleAutomorphism K a ha).conjAlgEquiv ℚ T.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K := by
  intro A hA
  obtain ⟨g, rfl⟩ := hA
  obtain ⟨g, rfl⟩ := a.surjective g
  have h := congrArg ((cosetModuleAutomorphism K a ha).conjAlgEquiv ℚ)
    (T.property (AbelianScheme.TateComparison.HeckeKernel.translate K g) ⟨g, rfl⟩)
  simpa only [map_mul, cosetConjugation_translate] using h

def heckeAutomorphism : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K →ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K :=
  (((cosetModuleAutomorphism K a ha).conjAlgEquiv ℚ).toAlgHom.comp
    (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K).val).codRestrict _ (cosetConjugation_spherical K a ha)

theorem heckeAutomorphism_kernel (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K (heckeAutomorphism K a ha T) =
      cosetModuleAutomorphism K a ha (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T) := by
  have hδ : cosetModuleAutomorphism K a ha (Finsupp.single (QuotientGroup.mk (1 : G)) 1) =
      Finsupp.single (QuotientGroup.mk (1 : G)) 1 := by
    rw [cosetModuleAutomorphism_single, cosetAutomorphism_mk, map_one]
  change cosetModuleAutomorphism K a ha (T.val
    ((cosetModuleAutomorphism K a ha).symm (Finsupp.single (QuotientGroup.mk (1 : G)) 1))) = _
  rw [← hδ, LinearEquiv.symm_apply_apply]
  rfl

end

/-! Finite kernel sums retain every coefficient under the actual coset
permutation induced by a level-preserving group automorphism. -/

open scoped Classical

variable {G : Type*} [Group G] (K : Subgroup G) (a : G ≃* G)
  (ha : ∀ g, a g ∈ K ↔ g ∈ K)

theorem cosetModuleAutomorphism_sum (v : AbelianScheme.TateComparison.HeckeKernel.CosetModule K) (f : G ⧸ K → ℂ) :
    (cosetModuleAutomorphism K a ha v).sum (fun x r => (r : ℂ) * f x) =
      v.sum (fun x r => (r : ℂ) * f (cosetAutomorphism K a ha x)) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [Finsupp.sum_add_index, add_mul, hv, hw]
  | single x r =>
      rw [cosetModuleAutomorphism_single]
      simp

theorem heckeAutomorphism_kernel_sum (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) (f : G ⧸ K → ℂ) :
    (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K (heckeAutomorphism K a ha T)).sum (fun x r => (r : ℂ) * f x) =
      (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T).sum (fun x r => (r : ℂ) * f (cosetAutomorphism K a ha x)) := by
  rw [heckeAutomorphism_kernel, cosetModuleAutomorphism_sum]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphism.Local
