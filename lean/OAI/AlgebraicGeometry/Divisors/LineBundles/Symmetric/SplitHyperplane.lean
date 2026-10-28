import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LinearEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Kernel
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricRegular
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularRingEquiv

/-! # Split Hyperplane -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.SplitHyperplane.BundleCycles

noncomputable section

/-! Splitting off a rank-one direct summand gives a genuine
regular homogeneous equation and its exact symmetric-algebra quotient. -/

variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] R × N)

def splitHyperplaneQuotient : M →ₗ[R] N := (LinearMap.snd R R N).comp e.toLinearMap

theorem splitHyperplaneQuotient_surjective : Function.Surjective (splitHyperplaneQuotient e) := by
  intro n
  exact ⟨e.symm (0, n), by change (e (e.symm (0, n))).2 = n; rw [e.apply_symm_apply]⟩

def splitHyperplaneEquation : SymmetricAlgebra R M := SymmetricAlgebra.ι R M (e.symm (1, 0))

theorem splitHyperplaneEquation_regular : IsRegular (splitHyperplaneEquation e) := by
  have h := RegularRingEquiv.BundleCycles.regular_ringEquiv (LinearEquiv.BundleCycles.symmetricLinearEquiv e.symm) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R N)
    (Augmented.SymmetricRegular.BundleCycles.augmentedSymmetricVariable_isRegular R N)
  have he : LinearEquiv.BundleCycles.symmetricLinearEquiv e.symm (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R N) = splitHyperplaneEquation e :=
    LinearEquiv.BundleCycles.symmetricLinearEquiv_generator e.symm (1, 0)
  exact he ▸ h

theorem splitHyperplaneEquation_kernel :
    RingHom.ker (GradedMap.BundleCycles.symmetricGradedMap (splitHyperplaneQuotient e)).toRingHom =
      Ideal.span {splitHyperplaneEquation e} := by
  have H := GradedMap.BundleCycles.symmetricGradedMap_comp e.toLinearMap (LinearMap.snd R R N)
  have hc : RingHom.ker (GradedMap.BundleCycles.symmetricGradedMap (splitHyperplaneQuotient e)).toRingHom =
      (RingHom.ker (GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R N)).toRingHom).comap
        (LinearEquiv.BundleCycles.symmetricLinearEquiv e).toRingHom := by
    ext a
    exact (congrArg (fun b => b = 0) (DFunLike.congr_fun H a)).symm.to_iff
  rw [hc, SymmetricInfinity.Kernel.BundleCycles.symmetricInfinity_kernel]
  change (Ideal.span {Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R N}).comap (LinearEquiv.BundleCycles.symmetricLinearEquiv e) = _
  rw [← Ideal.map_symm (LinearEquiv.BundleCycles.symmetricLinearEquiv e), Ideal.map_span, Set.image_singleton]
  exact congrArg (fun a => Ideal.span {a}) (LinearEquiv.BundleCycles.symmetricLinearEquiv_generator e.symm (1, 0))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.SplitHyperplane.BundleCycles
