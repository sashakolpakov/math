import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductQuotientRing
import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductDomain

/-! # Product Quotient Prime -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductQuotientPrime.Constructions

noncomputable section

/-! Over an algebraically closed field the product ideal of prime
supports is prime. This uses the actual quotient-product algebra
isomorphism and integrality of the tensor product of the supports. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalQuotient OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductQuotientRing.Constructions

universe u
variable (k R S : Type u) [Field k] [IsAlgClosed k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra.FiniteType k R]
  (I : Ideal R) (J : Ideal S) [I.IsPrime] [J.IsPrime]

theorem productIdeal_prime : (TorAlgebra.ExternalQuotient.productIdeal k R S I J).IsPrime := by
  let : IsDomain ((R ⧸ I) ⊗[k] (S ⧸ J)) := ProductDomain.Constructions.tensorProduct_isDomain
  apply (Ideal.Quotient.isDomain_iff_prime (TorAlgebra.ExternalQuotient.productIdeal k R S I J)).mp
  exact (ProductQuotientRing.Constructions.quotientProductEquiv k R S I J).toRingEquiv.toMulEquiv.isDomain

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductQuotientPrime.Constructions
