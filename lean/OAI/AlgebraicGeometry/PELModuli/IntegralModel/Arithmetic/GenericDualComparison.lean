import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.QuotientGeneric
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.TotalSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarIntrinsicComparison

/-! # Generic Dual Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericDualComparison

noncomputable section

/-! The actual prescribed universal dual on the arithmetic cover is
the pullback of the given ReferenceFamily universal dual on the generic quotient. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

namespace ArithmeticPELComparison
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N p : ℕ} [Fact p.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {V Q : Over B.base}

omit [Fact p.Prime] in
theorem generic_dual_family_comparison
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V)
    (π : V ⟶ Q) (d : (Over.pullback B.generic).obj Q ≅ ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M)
    (a : PEL.Iso.PolarizedActionIso
      ((ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).pullback ((Over.pullback B.generic).map π ≫ d.hom)).data
      (U.genericIntegralFamily B iota).forgetAuxiliary.data) :
    let D := (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).data.polarized.dual.abelian.pullback d.hom.left
    ∃ e : (Relative.ScalarFunctor.relativeScalarFunctor B.generic V).obj U.forgetAuxiliary.data.polarized.dual.abelian.scheme ≅
      (Over.pullback ((Over.pullback B.generic).map π).left).obj D.scheme, IsMonHom e.hom := by
  let A := U.forgetAuxiliary.data.polarized.dual.abelian.scheme
  let D := (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).data.polarized.dual.abelian
  let e₀ := Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison B.generic V A
  let e₁ := a.polarized.dual.symm
  let e₂ := D.pullbackCompIso d.hom.left ((Over.pullback B.generic).map π).left
  have : IsMonHom e₀.hom := Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison_isMonHom B.generic V A
  have : IsMonHom a.polarized.dual.hom := a.polarized.dualGroup
  have : IsMonHom e₁.hom := inferInstanceAs (IsMonHom a.polarized.dual.inv)
  have : IsMonHom e₂.hom := inferInstance
  have : IsMonHom (e₀.hom ≫ e₁.hom) := instIsMonHomComp e₀.hom e₁.hom
  refine ⟨e₀ ≪≫ e₁ ≪≫ e₂, ?_⟩
  change IsMonHom ((e₀.hom ≫ e₁.hom) ≫ e₂.hom)
  exact instIsMonHomComp (e₀.hom ≫ e₁.hom) e₂.hom

end ArithmeticPELComparison

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericDualComparison
