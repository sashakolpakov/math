import OAI.NumberTheory.PadicHodge.IntegralComparison.BasisSheafificationUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusLocalization

/-! # Frobenius Sheafification Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusSheafificationUnit

noncomputable section

/-! On actual affine étale charts, the original de Rham sheafification unit is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k C σ : Type u) [Field k] [Fintype k] [CommRing C] [Algebra k C] [LinearOrder σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.FormallyEtale (MvPolynomial σ k) C]

local notation "X" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C
local notation "J" => Opens.grothendieckTopology (Spec (CommRingCat.of C))

include σ in
theorem coordinate_principal (c : C) (n : ℕ) :
    IsIso ((toSheafify J (FrobeniusSections.presheaf k C n)).app
      (op (PrimeSpectrum.basicOpen c))) :=
  BasisSheafificationUnit.Localizing.principal (CommRingCat.of C) (FrobeniusSections.presheaf k C n)
    (fun a => FrobeniusLocalization.restriction k C σ a n) c

include σ in
theorem module_principal (c : C) (n : ℕ) :
    IsIso (Module.SheafificationUnit.unit k X ((Frobenius.DeRhamGlobal.presheafComplex k X).X n)
      (op (PrimeSpectrum.basicOpen c))) :=
  (Module.SheafificationUnit.scalar_isIso_iff C (ModuleScalars.base C)
    ((Frobenius.DeRhamGlobal.presheafComplex k X).X n) (op (PrimeSpectrum.basicOpen c))).mp
      (coordinate_principal k C σ c n)

include σ in
theorem base_principal (c : C) (n : ℕ) :
    IsIso ((toSheafify J ((AlgebraSheafScalars.presheaves k X).obj
      ((Frobenius.DeRhamGlobal.presheafComplex k X).X n))).app (op (PrimeSpectrum.basicOpen c))) :=
  (Module.SheafificationUnit.scalar_isIso_iff k X
    ((Frobenius.DeRhamGlobal.presheafComplex k X).X n) (op (PrimeSpectrum.basicOpen c))).mpr
      (module_principal k C σ c n)

include σ in
theorem forms_principal (c : C) (n : ℕ) :
    IsIso ((toSheafify J (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k X n)).app (op (PrimeSpectrum.basicOpen c))) := by
  let : IsIso ((toSheafify J ((AlgebraSheafScalars.presheaves k X).obj
      ((Frobenius.DeRhamGlobal.presheafComplex k X).X n))).app (op (PrimeSpectrum.basicOpen c))) :=
    base_principal k C σ c n
  exact SheafificationUnitIso.of_iso J (Frobenius.DeRhamGlobal.formsIso k X n) (op (PrimeSpectrum.basicOpen c))

include σ in
theorem forms_top (n : ℕ) :
    IsIso ((toSheafify J (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k X n)).app (op ⊤)) := by
  have h := forms_principal k C σ 1 n
  have hopen : (PrimeSpectrum.basicOpen (1 : C) : (Spec (CommRingCat.of C)).Opens) = ⊤ := PrimeSpectrum.basicOpen_one
  rwa [hopen] at h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusSheafificationUnit
