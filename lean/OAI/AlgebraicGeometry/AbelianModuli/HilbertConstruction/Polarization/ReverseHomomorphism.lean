import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.KernelAnnihilator
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismScalars

/-! # Reverse Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual polarization-type isogeny has a constructed reverse group homomorphism. Both composites are multiplication by its specified finite-flat degree. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
universe u

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.exists_reverseHomomorphism
    {S : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S} {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ}
    (hp : p.HasPolarizationType δ) (hδ : ∀ i, 0 < δ i) :
    ∃ m : B.scheme ⟶ A.scheme, IsMonHom m ∧
      p.hom ≫ m = A.multiplication ((∏ i, δ i) ^ 2) ∧
      m ≫ p.hom = B.multiplication ((∏ i, δ i) ^ 2) := by
  let d := (∏ i, δ i) ^ 2
  have hm : IsMonHom (A.multiplication d) := by
    rw [← A.endRing_natCast_hom d]
    infer_instance
  have hk : p.kernelInclusion ≫ A.multiplication d = 1 :=
    (A.comp_multiplication d p.kernelInclusion).trans (hp.kernelInclusion_pow_degree hδ)
  obtain ⟨m, hleft, _⟩ := p.existsUnique_group_kernel_factor A (A.multiplication d) hk
  have : Epi p.hom.left := Flat.epi_of_flat_of_surjective p.hom.left
  have : Epi p.hom := Functor.epi_of_epi_map (Over.forget S)
    (inferInstanceAs (Epi p.hom.left))
  refine ⟨m.val, m.property, hleft, ?_⟩
  apply (cancel_epi p.hom).mp
  rw [← Category.assoc, hleft]
  calc
    A.multiplication d ≫ p.hom = p.hom ^ d := by
      change ((𝟙 A.scheme) ^ d) ≫ p.hom = p.hom ^ d
      rw [MonObj.pow_comp, Category.id_comp]
    _ = p.hom ≫ B.multiplication d := (B.comp_multiplication d p.hom).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
