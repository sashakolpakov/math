import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseChangedCoefficientDerivations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.CoefficientDerivationKernel

/-! # Fiber Coefficient Derivation Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiberCoefficientDerivationKernel

noncomputable section

section

/-! Differences of affine lifts that kill the base identify linearly
with derivations on the actual fiber algebra. The comparison preserves
evaluation on every original regular function. -/

variable (k R S B C : Type) [CommRing k] [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra k R] [Algebra k S] [Algebra k B] [Algebra k C]
    [Algebra R k] [Algebra R S] [Algebra R B] [Algebra R C]
    [Algebra S B] [Algebra S C] [Algebra B C]
    [IsScalarTower k R S] [IsScalarTower k R C] [IsScalarTower k S C]
    [IsScalarTower R k B] [IsScalarTower R S B] [IsScalarTower R k C]
    [IsScalarTower R S C] [IsScalarTower k B C] [IsScalarTower S B C]
    [Algebra.IsPushout R k S B]

def fiberCoefficientDerivationKernelEquiv :
    (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).ker ≃ₗ[C] Derivation k B C :=
  (Relative.CoefficientDerivationKernel.relativeCoefficientDerivationKernelEquiv k R S C).trans
    (BaseChangedCoefficientDerivations.baseChangedCoefficientDerivationEquiv R k S B C)

omit [IsScalarTower k S C] in
theorem fiberCoefficientDerivationKernelEquiv_algebraMap
    (d : (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).ker) (s : S) :
    fiberCoefficientDerivationKernelEquiv k R S B C d (algebraMap S B s) = d.val s := by
  change BaseChangedCoefficientDerivations.baseChangedCoefficientDerivation R k S B C
    (Relative.CoefficientDerivationKernel.relativeCoefficientDerivationKernelEquiv k R S C d) (algebraMap S B s) = d.val s
  rw [BaseChangedCoefficientDerivations.baseChangedCoefficientDerivation_algebraMap, Relative.CoefficientDerivationKernel.relativeCoefficientDerivationKernelEquiv_apply]

end

/-! Ordered differences of linear affine lifts are linear derivations
on the actual fiber and satisfy the additive cocycle equation. -/

variable (k R S B C : Type) [CommRing k] [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra k R] [Algebra k S] [Algebra k B] [Algebra k C]
    [Algebra R k] [Algebra R S] [Algebra R B] [Algebra R C]
    [Algebra S B] [Algebra S C] [Algebra B C]
    [IsScalarTower k R S] [IsScalarTower k R C] [IsScalarTower k S C]
    [IsScalarTower R k B] [IsScalarTower R S B] [IsScalarTower R k C]
    [IsScalarTower R S C] [IsScalarTower k B C] [IsScalarTower S B C]
    [Algebra.IsPushout R k S B]
    {V : Type} [AddCommGroup V] [Module k V]
    (L M : V →ₗ[k] Derivation k S C)
    (h : ((Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).restrictScalars k).comp L =
      ((Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).restrictScalars k).comp M)

def linearLiftDifferenceKernel : V →ₗ[k] (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).ker :=
  LinearMap.codRestrict ((Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).ker.restrictScalars k)
    (M - L) (fun v => by
      change Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C (M v - L v) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (LinearMap.congr_fun h v).symm)

def linearFiberLiftDifference : V →ₗ[k] Derivation k B C :=
  ((fiberCoefficientDerivationKernelEquiv k R S B C).restrictScalars k).toLinearMap.comp
    (linearLiftDifferenceKernel k R S C L M h)

theorem linearFiberLiftDifference_algebraMap (v : V) (s : S) :
    linearFiberLiftDifference k R S B C L M h v (algebraMap S B s) = M v s - L v s := by
  exact fiberCoefficientDerivationKernelEquiv_algebraMap k R S B C
    (linearLiftDifferenceKernel k R S C L M h v) s

theorem linearFiberLiftDifference_cocycle (Q : V →ₗ[k] Derivation k S C)
    (hMQ : ((Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).restrictScalars k).comp M =
      ((Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).restrictScalars k).comp Q) :
    linearFiberLiftDifference k R S B C L M h + linearFiberLiftDifference k R S B C M Q hMQ =
      linearFiberLiftDifference k R S B C L Q (h.trans hMQ) := by
  apply LinearMap.ext
  intro v
  apply BaseChangedCoefficientDerivations.baseChangedCoefficientDerivation_ext R k S B C
  intro s
  change linearFiberLiftDifference k R S B C L M h v (algebraMap S B s) +
      linearFiberLiftDifference k R S B C M Q hMQ v (algebraMap S B s) = _
  rw [linearFiberLiftDifference_algebraMap, linearFiberLiftDifference_algebraMap,
    linearFiberLiftDifference_algebraMap]
  abel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiberCoefficientDerivationKernel
