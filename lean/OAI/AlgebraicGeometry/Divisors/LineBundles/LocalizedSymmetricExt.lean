import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarMap
import Mathlib.RingTheory.Localization.Module

/-! # Localized Symmetric Ext -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSymmetricExt.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual localized module generators determine symmetric-algebra maps -/

variable {R S M N T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]
    (D : Submonoid R) [IsLocalization D S] (f : M →ₗ[R] N) [IsLocalizedModule D f]

include D in
theorem localizedSymmetricRingHom_ext (g h : SymmetricAlgebra S N →+* T)
    (hc : ∀ s, g (algebraMap S (SymmetricAlgebra S N) s) = h (algebraMap S (SymmetricAlgebra S N) s))
    (hm : ∀ m, g (SymmetricAlgebra.ι S N (f m)) = h (SymmetricAlgebra.ι S N (f m))) : g = h := by
  refine Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext g h hc ?_
  intro n
  obtain ⟨⟨m, d⟩, hn⟩ := IsLocalizedModule.surj D f n
  have he : algebraMap S (SymmetricAlgebra S N) (algebraMap R S d.val) * SymmetricAlgebra.ι S N n =
      SymmetricAlgebra.ι S N (f m) := by
    rw [← Algebra.smul_def, ← map_smul, algebraMap_smul]
    exact congrArg (SymmetricAlgebra.ι S N) hn
  have hu := ((IsLocalization.map_units S d).map (algebraMap S (SymmetricAlgebra S N))).map g
  apply hu.mul_right_inj.mp
  rw [← map_mul g, he, hc (algebraMap R S d.val), ← map_mul h, he]
  exact hm m

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSymmetricExt.BundleCycles
