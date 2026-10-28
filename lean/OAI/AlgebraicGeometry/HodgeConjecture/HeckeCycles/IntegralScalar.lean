import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Perfect
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.EigenlineCharacter
import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Integral Scalar -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralScalar.CM

noncomputable section

/-! Projective stabilization by integral SL3 is literal stabilization.
The local-ring perfectness proof removes the scalar character, without
a continuity assumption on the representation or character. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.EigenlineCharacter.TestTransport

variable (q : ℕ) [Fact q.Prime]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →* (V ≃ₗ[ℂ] V)) (v : V)

theorem fixed
    (hline : ∀ u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q, ∃ c : ℂˣ, ρ u v = (c : ℂ) • v) :
    ∀ u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q, ρ u v = v := by
  by_cases hv : v = 0
  · subst v
    intro u _
    exact map_zero (ρ u)
  let f : Matrix.SpecialLinearGroup (Fin 3) (PadicInt q) →* RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q :=
    Matrix.SpecialLinearGroup.map (PadicInt.Coe.ringHom (p := q))
  let ρ₀ := ρ.comp f
  have hline₀ (g : Matrix.SpecialLinearGroup (Fin 3) (PadicInt q)) :
      ∃ c : ℂˣ, ρ₀ g v = (c : ℂ) • v := hline (f g) ⟨g, rfl⟩
  let χ := CMExtraction.EigenlineCharacter.TestTransport.eigenlineCharacter ρ₀ v hv hline₀
  have hχ (g : Matrix.SpecialLinearGroup (Fin 3) (PadicInt q)) : χ g = 1 := by
    apply Abelianization.commutator_subset_ker χ
    rw [Local.Perfect.CM.commutator_eq_top]
    exact Subgroup.mem_top g
  rintro u ⟨g, rfl⟩
  exact (CMExtraction.EigenlineCharacter.TestTransport.eigenlineCharacter_spec ρ₀ v hv hline₀ g).trans
    (by rw [hχ g, Units.val_one, one_smul])

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralScalar.CM
