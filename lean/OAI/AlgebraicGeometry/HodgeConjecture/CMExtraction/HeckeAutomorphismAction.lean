import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphism
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient

/-! # Hecke Automorphism Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphismAction.Local

noncomputable section

/-! Exact transport of the finite spherical coset-sum action, including
the inverse-transpose convention forced by the native finite Weil model. -/

open scoped Classical TensorProduct

variable {G : Type*} [Group G] (K : Subgroup G) (a : G ≃* G)
  (ha : ∀ g, a g ∈ K ↔ g ∈ K)

theorem cosetAutomorphism_involutive (h : Function.Involutive a) :
    Function.Involutive (HeckeAutomorphism.Local.cosetAutomorphism K a ha) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [HeckeAutomorphism.Local.cosetAutomorphism_mk, HeckeAutomorphism.Local.cosetAutomorphism_mk, h g]

theorem cosetModuleAutomorphism_involutive (h : Function.Involutive a) :
    Function.Involutive (HeckeAutomorphism.Local.cosetModuleAutomorphism K a ha) := by
  intro v
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single x r =>
      rw [HeckeAutomorphism.Local.cosetModuleAutomorphism_single, HeckeAutomorphism.Local.cosetModuleAutomorphism_single,
        cosetAutomorphism_involutive K a ha h x]

theorem heckeAutomorphism_involutive (h : Function.Involutive a) :
    Function.Involutive (HeckeAutomorphism.Local.heckeAutomorphism K a ha) := by
  intro T
  apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective K
  change RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K (HeckeAutomorphism.Local.heckeAutomorphism K a ha (HeckeAutomorphism.Local.heckeAutomorphism K a ha T)) =
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T
  rw [HeckeAutomorphism.Local.heckeAutomorphism_kernel, HeckeAutomorphism.Local.heckeAutomorphism_kernel]
  exact cosetModuleAutomorphism_involutive K a ha h (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : G →* (V ≃ₗ[ℂ] V))

def automorphismFixedInput (φ : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs K ρ) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs K (ρ.comp a.toMonoidHom) :=
  ⟨φ.val, fun g hg => φ.property (a g) ((ha g).mpr hg)⟩

variable [Module ℚ V] [IsScalarTower ℚ ℂ V]

omit [IsScalarTower ℚ ℂ V] in
theorem evaluateKernel_automorphism (φ : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs K ρ) (v : AbelianScheme.TateComparison.HeckeKernel.CosetModule K) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ φ (HeckeAutomorphism.Local.cosetModuleAutomorphism K a ha v) =
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K (ρ.comp a.toMonoidHom) (automorphismFixedInput K a ha ρ φ) v := by
  have h : (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ φ).comp (HeckeAutomorphism.Local.cosetModuleAutomorphism K a ha).toLinearMap =
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K (ρ.comp a.toMonoidHom) (automorphismFixedInput K a ha ρ φ) := by
    apply Finsupp.lhom_ext
    intro x r
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    change RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ φ
      (HeckeAutomorphism.Local.cosetModuleAutomorphism K a ha (Finsupp.single (QuotientGroup.mk g) r)) = _
    rw [HeckeAutomorphism.Local.cosetModuleAutomorphism_single, HeckeAutomorphism.Local.cosetAutomorphism_mk]
    simp only [RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel, Finsupp.linearCombination_single, RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.cosetValue_mk]
    rfl
  exact LinearMap.congr_fun h v

theorem weilOperator_automorphism (φ : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs K ρ) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K ρ (HeckeAutomorphism.Local.heckeAutomorphism K a ha T) φ.val =
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K (ρ.comp a.toMonoidHom) T φ.val := by
  rw [RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator_eq_evaluateKernel, HeckeAutomorphism.Local.heckeAutomorphism_kernel, evaluateKernel_automorphism]
  exact (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator_eq_evaluateKernel K (ρ.comp a.toMonoidHom) T
    (automorphismFixedInput K a ha ρ φ)).symm

def contragredientHecke (q : ℕ) [Fact q.Prime] : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q :=
  AlgEquiv.ofBijective (HeckeAutomorphism.Local.heckeAutomorphism (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Contragredient.Local.contragredientEquiv ℚ_[q])
    (Contragredient.Local.contragredient_integral_iff q))
    (heckeAutomorphism_involutive (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Contragredient.Local.contragredientEquiv ℚ_[q])
      (Contragredient.Local.contragredient_integral_iff q) (Contragredient.Local.contragredient_involutive ℚ_[q])).bijective

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphismAction.Local
