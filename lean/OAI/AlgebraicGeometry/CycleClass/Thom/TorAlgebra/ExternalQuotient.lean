import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorSquare
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorQuotientCoefficient

/-! # External Quotient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalQuotient

noncomputable section

/-! For two quotient modules, the external coefficient is the actual
quotient of the tensor algebra by their extended ideals. The two maps
are explicitly the right and left tensor inclusions. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorSquare OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorQuotientCoefficient

universe u
variable (k R S : Type u) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def productIdeal (I : Ideal R) (J : Ideal S) : Ideal (R ⊗[k] S) :=
  J.map (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := S)).toRingHom ⊔
    I.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := R) (B := S)).toRingHom

def productQuotientIso (I : Ideal R) (J : Ideal S) :
    ExternalTensorSquare.externalCoefficient k R S (ModuleCat.of S (S ⧸ J)) (ModuleCat.of R (R ⧸ I)) ≅
      ModuleCat.of (R ⊗[k] S) ((R ⊗[k] S) ⧸ productIdeal k R S I J) :=
  TensorQuotientCoefficient.coefficientQuotientIso R (R ⊗[k] S) S I J

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalQuotient
