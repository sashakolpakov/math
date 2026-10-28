import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialSpectralFunctions
import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedGeneralLinearAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedInfinitesimalRelations

/-! # Additive Spectral Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AdditiveSpectralAction.Construction

noncomputable section

/-! Additive changes of diagonal eigenvalues preserve the defining ideal.
This is the algebraic Lie-algebra property used to extract split weights. -/

open scoped Classical

theorem additive_map_finsupp_weight
    {k σ : Type*} [Field k] [Fintype σ] (ψ : k →+ k) (w : σ → k) (m : σ →₀ ℕ) :
    Finsupp.weight (fun i => ψ (w i)) m = ψ (Finsupp.weight w m) := by
  simp only [Finsupp.weight_eq_sum, map_sum, map_nsmul]

theorem boundedInfinitesimal_conjugated_monomial_eigenvector
    {k : Type} [Field k] {n : ℕ} (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) k)
    (w : Fin n → k) (m : BoundedMonomialBasis.Construction.BoundedMonomials n d) :
    Infinitesimal.Degree.Construction.boundedInfinitesimal d (g.val * Matrix.diagonal w * (g⁻¹).val)
        (BoundedGeneralLinearAction.Construction.boundedPolynomialUnitEquiv d g (BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d m)) =
      Finsupp.weight (fun ij : Fin n × Fin n => w ij.2) m.val •
        BoundedGeneralLinearAction.Construction.boundedPolynomialUnitEquiv d g (BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d m) := by
  have h := LinearMap.congr_fun (BoundedGeneralLinearAction.Construction.boundedInfinitesimal_unit_intertwining d g (Matrix.diagonal w))
    (BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d m)
  have hd : Infinitesimal.Degree.Construction.boundedInfinitesimal d (Matrix.diagonal w) (BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d m) =
      Finsupp.weight (fun ij : Fin n × Fin n => w ij.2) m.val •
        BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d m := by
    apply Subtype.ext
    change Infinitesimal.Action.Construction.rightInfinitesimal (Matrix.diagonal w) (BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d m).val =
      Finsupp.weight (fun ij : Fin n × Fin n => w ij.2) m.val •
        (BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d m).val
    rw [BoundedMonomialBasis.Construction.boundedMonomialBasisRaw_val, BoundedDiagonalAction.Construction.rightInfinitesimal_diagonal, BoundedDiagonalAction.Construction.scalarWeightDerivation_monomial]
  change BoundedGeneralLinearAction.Construction.boundedPolynomialUnitEquiv d g (Infinitesimal.Degree.Construction.boundedInfinitesimal d (Matrix.diagonal w)
    (BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d m)) = _ at h
  rw [hd, map_smul] at h
  exact h.symm

theorem boundedInfinitesimal_additive_spectral_polynomial
    {k : Type} [Field k] {n : ℕ} (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) k)
    (w : Fin n → k) (ψ : k →+ k) :
    ∃ p : Polynomial k,
      Polynomial.aeval (Infinitesimal.Degree.Construction.boundedInfinitesimal d (g.val * Matrix.diagonal w * (g⁻¹).val)) p =
        Infinitesimal.Degree.Construction.boundedInfinitesimal d (g.val * Matrix.diagonal (fun i => ψ (w i)) * (g⁻¹).val) := by
  apply PolynomialSpectralFunctions.Construction.eigenvalue_function_is_polynomial
    ((BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d).map (BoundedGeneralLinearAction.Construction.boundedPolynomialUnitEquiv d g))
    _ _ (fun m => Finsupp.weight (fun ij : Fin n × Fin n => w ij.2) m.val) ψ
  · exact boundedInfinitesimal_conjugated_monomial_eigenvector d g w
  · intro m
    rw [Module.Basis.map_apply,
      boundedInfinitesimal_conjugated_monomial_eigenvector, additive_map_finsupp_weight]

theorem infinitesimal_additive_spectral_matrix
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (g : Matrix.GeneralLinearGroup (Fin n) k) (w : Fin n → k) (ψ : k →+ k)
    (hG : g.val * Matrix.diagonal w * (g⁻¹).val ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    g.val * Matrix.diagonal (fun i => ψ (w i)) * (g⁻¹).val ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G := by
  apply (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G _).mpr
  intro p hp
  let d := p.totalDegree
  let q : BoundedRepresentation.Construction.BoundedPolynomials k n d :=
    ⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl⟩
  obtain ⟨r, hr⟩ := boundedInfinitesimal_additive_spectral_polynomial d g w ψ
  have hq : q ∈ BoundedRepresentation.Construction.boundedIdealSubspace G d := hp
  have h := Polynomial.aeval_apply_smul_mem_of_le_comap hq r
    (Infinitesimal.Degree.Construction.boundedInfinitesimal d (g.val * Matrix.diagonal w * (g⁻¹).val))
    (BoundedInfinitesimalRelations.Construction.boundedInfinitesimal_preserves_ideal G d _ hG)
  rw [hr] at h
  exact h

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AdditiveSpectralAction.Construction
