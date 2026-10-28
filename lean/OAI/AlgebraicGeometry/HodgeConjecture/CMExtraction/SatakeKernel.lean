import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeScalarExtension
import OAI.RepresentationTheory.Satake.GL3TorusIwasawa

/-! # Satake Kernel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeKernel.Iwasawa

noncomputable section

/-! Evaluation of the actual constant term and normalized transform as
finite sums of the original rational Hecke kernel. -/

open scoped Classical TensorProduct

variable {G L : Type*} [Group G] [AddCommGroup L] {K : Subgroup G}

def evaluateLattice (χ : Multiplicative L →* ℂ) : AddMonoidAlgebra ℂ L →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ L χ

theorem evaluateLattice_single (χ : Multiplicative L →* ℂ) (ell : L) (c : ℂ) :
    evaluateLattice χ (AddMonoidAlgebra.single ell c) = c * χ (Multiplicative.ofAdd ell) :=
  AddMonoidAlgebra.lift_single χ ell c

theorem evaluate_pushforward (D : RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.Decomposition K L)
    (χ : Multiplicative L →* ℂ) (v : RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.CosetModule K) :
    evaluateLattice χ (D.pushforward v) =
      v.sum (fun x c => c * χ (Multiplicative.ofAdd (D.height x))) := by
  change evaluateLattice χ (Finsupp.linearCombination ℂ _ v) = _
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul, evaluateLattice_single, one_mul, smul_eq_mul]

theorem rationalComplexHecke_kernel_map (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) :
    RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.kernel K (HeckeScalarExtension.Iwasawa.rationalComplexHecke K T) =
      (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T).mapRange (algebraMap ℚ ℂ) (map_zero _) := by
  ext x
  exact HeckeScalarExtension.Iwasawa.rationalComplexHecke_kernel K T x

theorem evaluate_constantTerm_rational (D : RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.Decomposition K L)
    (χ : Multiplicative L →* ℂ) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K) :
    evaluateLattice χ (D.constantTerm (HeckeScalarExtension.Iwasawa.rationalComplexHecke K T)) =
      (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T).sum
        (fun x a => (a : ℂ) * χ (Multiplicative.ofAdd (D.height x))) := by
  change evaluateLattice χ (D.pushforward (RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.kernel K (HeckeScalarExtension.Iwasawa.rationalComplexHecke K T))) = _
  rw [evaluate_pushforward, rationalComplexHecke_kernel_map, Finsupp.sum_mapRange_index]
  all_goals simp

theorem evaluate_twist (χ : Multiplicative L →* ℂ)
    (w : Multiplicative L →* ℂˣ) (f : AddMonoidAlgebra ℂ L) :
    evaluateLattice χ (RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.twist w f) =
      evaluateLattice (((Units.coeHom ℂ).comp w) * χ) f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single ell c =>
      rw [RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.twist_single, evaluateLattice_single, evaluateLattice_single]
      exact mul_assoc _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeKernel.Iwasawa
