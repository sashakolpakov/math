import Mathlib.LinearAlgebra.BilinearMap

/-! # Pair Bilinear Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairBilinearMaps.Construction

/-! Composing two bilinear inputs with a bilinear output gives an
actual four-linear map, using the standard linear composition maps. -/

universe u v

variable {K : Type u} [CommSemiring K]
  {A B C D AB CD W : Type v}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [AddCommMonoid AB] [AddCommMonoid CD] [AddCommMonoid W]
  [Module K A] [Module K B] [Module K C] [Module K D]
  [Module K AB] [Module K CD] [Module K W]

def pairBilinearLinearMap (b : A →ₗ[K] B →ₗ[K] AB) (c : C →ₗ[K] D →ₗ[K] CD)
    (d : AB →ₗ[K] CD →ₗ[K] W) : A →ₗ[K] B →ₗ[K] C →ₗ[K] D →ₗ[K] W :=
  b.compr₂ ((((LinearMap.llcomp K C (D →ₗ[K] CD) (D →ₗ[K] W)).flip c).comp
    (LinearMap.llcomp K D CD W)).comp d)

theorem pairBilinearLinearMap_apply (b : A →ₗ[K] B →ₗ[K] AB) (c : C →ₗ[K] D →ₗ[K] CD)
    (d : AB →ₗ[K] CD →ₗ[K] W) (a : A) (b' : B) (c' : C) (d' : D) :
    pairBilinearLinearMap b c d a b' c' d' = d (b a b') (c c' d') := rfl

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairBilinearMaps.Construction
