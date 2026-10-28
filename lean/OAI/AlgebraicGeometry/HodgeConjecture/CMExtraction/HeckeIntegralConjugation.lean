import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphism

/-! # Hecke Integral Conjugation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeIntegralConjugation.Local

noncomputable section

/-! Integral conjugation does not change the induced spherical operator.
This allows an inverse-transpose automorphism to be compared using a
Borel-preserving integral Weyl conjugate. -/

open scoped Classical

variable {G : Type*} [Group G] (K : Subgroup G) (a b : G ≃* G)
  (ha : ∀ g, a g ∈ K ↔ g ∈ K) (hb : ∀ g, b g ∈ K ↔ g ∈ K)
  (k : G) (hk : k ∈ K) (hab : ∀ g, b g = k * a g * k⁻¹)

include hk hab in
theorem cosetAutomorphism_integral_conjugation (x : G ⧸ K) :
    HeckeAutomorphism.Local.cosetAutomorphism K b hb x = k • HeckeAutomorphism.Local.cosetAutomorphism K a ha x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [HeckeAutomorphism.Local.cosetAutomorphism_mk, HeckeAutomorphism.Local.cosetAutomorphism_mk]
  change QuotientGroup.mk (b g) = QuotientGroup.mk (k * a g)
  apply QuotientGroup.eq.mpr
  rw [hab]
  simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel, mul_one] using hk

include hk hab in
theorem cosetModuleAutomorphism_integral_conjugation (v : AbelianScheme.TateComparison.HeckeKernel.CosetModule K) :
    HeckeAutomorphism.Local.cosetModuleAutomorphism K b hb v =
      AbelianScheme.TateComparison.HeckeKernel.translate K k (HeckeAutomorphism.Local.cosetModuleAutomorphism K a ha v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single x r =>
      rw [HeckeAutomorphism.Local.cosetModuleAutomorphism_single, HeckeAutomorphism.Local.cosetModuleAutomorphism_single,
        AbelianScheme.TateComparison.HeckeKernel.translate_single, cosetAutomorphism_integral_conjugation K a b ha hb k hk hab]

include hk hab in
theorem heckeAutomorphism_integral_conjugation (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) :
    HeckeAutomorphism.Local.heckeAutomorphism K b hb T = HeckeAutomorphism.Local.heckeAutomorphism K a ha T := by
  apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective K
  change RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K (HeckeAutomorphism.Local.heckeAutomorphism K b hb T) = RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K (HeckeAutomorphism.Local.heckeAutomorphism K a ha T)
  rw [HeckeAutomorphism.Local.heckeAutomorphism_kernel,
    cosetModuleAutomorphism_integral_conjugation K a b ha hb k hk hab,
    ← HeckeAutomorphism.Local.heckeAutomorphism_kernel, RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel_fixed K _ k hk]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeIntegralConjugation.Local
