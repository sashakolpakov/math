import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualAt
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ComplementaryIsogeny

/-! # Quotient Dual Existence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualExistence.Construction

noncomputable section

/-! A scalar-killed finite quotient of the original polarized abelian
variety has constructed native dual data; no target dual is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {d : ℕ}
variable {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hn : 0 < n)
variable (hkernel : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme),
  x ≫ f.hom = 1 → x ^ n = 1)

def isogenousQuotientDualData : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B :=
  QuotientDualAt.Construction.quotientDualData D (ComplementaryIsogeny.Construction.exists_complementary_isogeny D ell f n hn hkernel).choose f

include D ell f n hn hkernel in
theorem exists_isogenousQuotientDualData : Nonempty (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) :=
  ⟨isogenousQuotientDualData D ell f n hn hkernel⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualExistence.Construction
