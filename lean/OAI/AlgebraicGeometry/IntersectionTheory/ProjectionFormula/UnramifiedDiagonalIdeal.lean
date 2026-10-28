import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.TensorKernel
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IdempotentKernel
import Mathlib.RingTheory.Unramified.Basic

/-! # Unramified Diagonal Ideal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnramifiedDiagonalIdeal

noncomputable section

/-! Over an unramified intermediate algebra, the relative diagonal
ideal is idempotent. Nakayama's lemma therefore removes it at a local
point of the absolute diagonal. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u

variable (K P A : Type u) [CommRing K] [CommRing P] [CommRing A]
  [Algebra K P] [Algebra K A] [Algebra P A] [IsScalarTower K P A]

theorem preimage :
    (KaehlerDifferential.ideal P A).comap (Relative.TensorKernel.map K P A).toRingHom =
      KaehlerDifferential.ideal K A := by
  change (RingHom.ker (Algebra.TensorProduct.lmul' P (S := A)).toRingHom).comap
    (Relative.TensorKernel.map K P A).toRingHom =
      RingHom.ker (Algebra.TensorProduct.lmul' K (S := A)).toRingHom
  rw [RingHom.comap_ker]
  apply congrArg RingHom.ker
  ext a <;> rfl

theorem localized [Algebra.FormallyUnramified P A]
    (L : Type u) [CommRing L] [IsNoetherianRing L] [IsLocalRing L]
    (g : A ⊗[K] A →+* L) (hp : (KaehlerDifferential.ideal K A).map g ≠ ⊤) :
    (KaehlerDifferential.ideal K A).map g =
      (RingHom.ker (Relative.TensorKernel.map K P A).toRingHom).map g := by
  have hi : KaehlerDifferential.ideal P A * KaehlerDifferential.ideal P A = KaehlerDifferential.ideal P A :=
    (Ideal.cotangent_subsingleton_iff _).mp (inferInstanceAs (Subsingleton Ω[A⁄P]))
  have h := Local.IdempotentKernel.localized (A ⊗[K] A) (A ⊗[P] A) L
    (Relative.TensorKernel.map K P A).toRingHom (Relative.TensorKernel.surjective K P A)
    (KaehlerDifferential.ideal P A) hi g (by rwa [preimage])
  rwa [preimage] at h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnramifiedDiagonalIdeal
