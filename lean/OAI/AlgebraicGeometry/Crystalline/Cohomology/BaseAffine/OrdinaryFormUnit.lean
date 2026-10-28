import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormCoherence
import OAI.NumberTheory.PadicHodge.IntegralComparison.BasisSheafificationUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitIso

/-! # Ordinary Form Unit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormUnit.BaseAffineOrdinaryFormUnit

noncomputable section

/-! # The canonical ordinary-form sheafification unit on affine etale charts -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A] [LinearOrder σ]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme R A
local notation "J" => Opens.grothendieckTopology (Spec (CommRingCat.of A))
local notation "M" => OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormBase.OrdinaryFormModulePresheaf.presheaf R (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X)

include σ in
theorem coordinate_top (n : ℕ) :
    IsIso ((toSheafify J (OrdinaryFormSections.BaseAffineOrdinaryFormSections.presheaf R A n)).app (op ⊤)) :=
  NumberTheory.PadicHodge.IntegralComparison.BasisSheafificationUnit.Localizing.top (CommRingCat.of A) (OrdinaryFormSections.BaseAffineOrdinaryFormSections.presheaf R A n)
    (fun a => OrdinaryFormCoherence.BaseAffineOrdinaryFormCoherence.restriction R A σ a n)

include σ in
theorem module_top (n : ℕ) : IsIso (NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationUnit.unit R X (M n) (op ⊤)) :=
  (NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationUnit.scalar_isIso_iff A (NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars.base A) (M n) (op ⊤)).mp
    (coordinate_top R A σ n)

include σ in
theorem forms_top (n : ℕ) : IsIso ((toSheafify J (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).app (op ⊤)) := by
  let : IsIso ((toSheafify J ((NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.presheaves R X).obj (M n))).app (op ⊤)) :=
    (NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationUnit.scalar_isIso_iff R X (M n) (op ⊤)).mpr (module_top R A σ n)
  exact NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitIso.of_iso J
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.underlyingIso R (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X) n) (op ⊤)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormUnit.BaseAffineOrdinaryFormUnit
