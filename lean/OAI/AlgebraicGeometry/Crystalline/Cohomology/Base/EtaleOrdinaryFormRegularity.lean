import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Etale Ordinary Form Regularity -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleOrdinaryFormRegularity.BaseEtaleOrdinaryFormRegularity

noncomputable section

/-! # Scalar regularity of actual ordinary forms and affine sheaf sections -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [LinearOrder σ] [Algebra (MvPolynomial σ R) A]
  [IsScalarTower R (MvPolynomial σ R) A] [Algebra.Etale (MvPolynomial σ R) A]

include σ in
theorem flat (n : ℕ) : Module.Flat R (DeRhamPresentationTo.DeRhamPresentation.Form R A n) := by
  let : Module.Flat R A := Module.Flat.trans R (MvPolynomial σ R) A
  let : Module.Free A (DeRhamPresentationTo.DeRhamPresentation.Form R A n) :=
    Module.Free.of_basis (NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.basis R A σ n)
  exact Module.Flat.trans R A (DeRhamPresentationTo.DeRhamPresentation.Form R A n)

include σ in
theorem forms (n : ℕ) (r : R) (hr : r ∈ nonZeroDivisors R) :
    IsSMulRegular (DeRhamPresentationTo.DeRhamPresentation.Form R A n) r := by
  let : Module.Flat R (DeRhamPresentationTo.DeRhamPresentation.Form R A n) := flat R A σ n
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors hr

include σ in
theorem global (n : ℕ) (r : R) (hr : r ∈ nonZeroDivisors R) :
    IsSMulRegular
      (((DeRhamGlobalId.DeRhamGlobal.sheafComplex R (BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme R A)).X n).obj.obj (op ⊤)) r := by
  let e := (BaseAffine.OrdinaryFormGlobal.BaseAffineOrdinaryFormGlobal.globalIso R A σ n).toLinearEquiv
  intro x y h
  apply e.injective
  apply forms R A σ n r hr
  exact ((e.map_smul r x).symm.trans (congrArg e h)).trans (e.map_smul r y)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleOrdinaryFormRegularity.BaseEtaleOrdinaryFormRegularity
