import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.PolarizedLevelProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ComplexDualTests
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.BaseChange

/-! # PEL Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.PELProduct

noncomputable section

/-! The normalized polarized product retains the original integral
action and gives an actual isomorphism of PEL families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (κ : K →+* ℂ) (A : PEL.Objects.PELObject P iota N (PEL.ComplexDualTests.pelComplexDualTest κ))
    (e : A.polarized.abelian.scheme ≅
      ((A.polarized.abelian.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)).scheme)
    [heGroup : IsMonHom e.hom]

def normalizedPELProduct (he : NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e) :
    PEL.Objects.PELIso A ((A.pullback (PEL.ComplexDualTests.pelComplexDualReduction κ)).pullback (PEL.ComplexDualTests.pelComplexDualProjection κ)) where
  polarized := PolarizedLevelProduct.normalizedPolarizedLevelProduct A.polarized e he
  action a := NormalizedDual.ProductAction.normalizedDualProduct_action A.polarized.abelian A.action e he a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.PELProduct
