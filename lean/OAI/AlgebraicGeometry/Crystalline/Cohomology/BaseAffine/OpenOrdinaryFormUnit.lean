import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormUnit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity
import OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitIso

/-! # Open Ordinary Form Unit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenOrdinaryFormUnit.BaseAffineOpenOrdinaryFormUnit

noncomputable section

/-! The canonical ordinary-form unit is invertible in every degree on affine opens with etale coordinates over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (U : X.left.Opens) (hU : IsAffineOpen U)
  (σ : Type u) [LinearOrder σ] [Algebra (MvPolynomial σ R) (OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X U)]
  [IsScalarTower R (MvPolynomial σ R) (OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X U)]
  [Algebra.Etale (MvPolynomial σ R) (OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X U)]

local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X U
local notation "Z" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme R A
local notation "g" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.chart R X U hU

include hU σ in
theorem forms (n : ℕ) : IsIso ((toSheafify (Opens.grothendieckTopology X.left)
    (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).app (op U)) := by
  let : IsOpenImmersion (g).left := OpenFormRegularity.BaseAffineOpenFormRegularity.chart_open R X U hU
  let : IsIso ((toSheafify (Opens.grothendieckTopology (Z).left)
      (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Z n)).app (op ⊤)) :=
    OrdinaryFormUnit.BaseAffineOrdinaryFormUnit.forms_top R A σ n
  let : IsIso ((toSheafify (Opens.grothendieckTopology (Z).left)
      ((g).left.opensFunctor.op ⋙ DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).app (op ⊤)) :=
    NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitIso.of_iso (Opens.grothendieckTopology (Z).left)
      (NumberTheory.PadicHodge.GeometricComparison.OpenForms.OpenFormsSheaves.presheafIso g n).symm (op ⊤)
  have h := NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitRestriction.isIso (g).left.opensFunctor (ModuleCat.{u} R)
    (Opens.grothendieckTopology (Z).left) (Opens.grothendieckTopology X.left)
    (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n) (op ⊤)
  have hopen : (g).left ''ᵁ ⊤ = U :=
    (Scheme.Hom.image_top_eq_opensRange (g).left).trans hU.opensRange_fromSpec
  exact hopen ▸ h

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenOrdinaryFormUnit.BaseAffineOpenOrdinaryFormUnit
