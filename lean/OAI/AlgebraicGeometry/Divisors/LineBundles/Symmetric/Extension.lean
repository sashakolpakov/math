import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-! # Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Extension.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual symmetric-algebra extension with its proved generator formula -/

variable {R M A : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [CommSemiring A] [Algebra R A]

def symmetricExtension (f : M →ₗ[R] A) :
    {g : SymmetricAlgebra R M →+* A //
      (∀ m, g (SymmetricAlgebra.ι R M m) = f m) ∧
      ∀ r, g (algebraMap R (SymmetricAlgebra R M) r) = algebraMap R A r} :=
  ⟨(SymmetricAlgebra.lift f).toRingHom, SymmetricAlgebra.lift_ι_apply f, (SymmetricAlgebra.lift f).commutes⟩

theorem symmetricExtension_generator (f : M →ₗ[R] A) (m : M) :
    (symmetricExtension f).val (SymmetricAlgebra.ι R M m) = f m :=
  (symmetricExtension f).property.1 m

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Extension.BundleCycles
