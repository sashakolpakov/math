import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Spherical Multiplication -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SphericalMultiplication.Radial

noncomputable section

/-! Multiplication of the actual finite spherical coset sums. The
endomorphism convention first gives the reversed composition law. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Geometric.SphericalGU.Spherical

variable {G S : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
  [Module ℚ S] [IsScalarTower ℚ ℂ S]
  (K : Subgroup G) (ρ : G →* (S ≃ₗ[ℂ] S))

theorem evaluateKernel_hecke (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) (φ : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs K ρ) (v : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.CosetModule K) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ φ (T.val v) = RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilAction K ρ T φ) v := by
  have h : (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ φ).comp T.val = RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilAction K ρ T φ) := by
    apply Finsupp.lhom_ext
    intro c r
    induction c using Quotient.inductionOn with
    | h g =>
        have h1 : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ φ (T.val (Finsupp.single (QuotientGroup.mk g) 1)) =
            RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilAction K ρ T φ) (Finsupp.single (QuotientGroup.mk g) 1) := by
          rw [AbelianScheme.TateComparison.HeckeKernel.hecke_single, RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel_translate]
          simp only [RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel, Finsupp.linearCombination_single, one_smul, RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.cosetValue_mk]
          congr 1
          exact (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator_eq_evaluateKernel K ρ T φ).symm
        have hr := congrArg (fun x : S => r • x) h1
        change RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ φ (T.val (Finsupp.single (QuotientGroup.mk g) r)) =
          RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilAction K ρ T φ) (Finsupp.single (QuotientGroup.mk g) r)
        simpa only [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one] using hr
  exact LinearMap.congr_fun h v

theorem weilAction_mul_reverse (T U : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) (φ : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs K ρ) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilAction K ρ (T * U) φ = RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilAction K ρ U (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilAction K ρ T φ) := by
  apply Subtype.ext
  change RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K ρ (T * U) φ.val =
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K ρ U (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilAction K ρ T φ).val
  rw [RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator_eq_evaluateKernel]
  change RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ φ (T.val (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K U)) = _
  rw [evaluateKernel_hecke, RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator_eq_evaluateKernel]

theorem weilAction_one (φ : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs K ρ) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilAction K ρ 1 φ = φ := by
  apply Subtype.ext
  change RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K ρ 1 φ.val = φ.val
  rw [RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator_eq_evaluateKernel]
  change RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel K ρ φ (Finsupp.single (QuotientGroup.mk 1) 1) = φ.val
  simp [RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.evaluateKernel]

def weilActionLinear : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K →ₗ[ℚ] Module.End ℂ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs K ρ) where
  toFun := RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilAction K ρ
  map_add' T U := by
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    change RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K ρ (T + U) φ.val =
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K ρ T φ.val + RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K ρ U φ.val
    have hk : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K (T + U) = RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T + RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K U := rfl
    simp only [RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator_eq_evaluateKernel, hk, map_add]
  map_smul' r T := by
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    change RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K ρ (r • T) φ.val = r • RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K ρ T φ.val
    have hk : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K (r • T) = r • RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T := rfl
    simp only [RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator_eq_evaluateKernel, hk, map_smul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SphericalMultiplication.Radial
