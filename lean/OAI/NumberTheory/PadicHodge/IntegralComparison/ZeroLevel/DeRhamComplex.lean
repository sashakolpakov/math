import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.FormFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.BaseQuotientDifferential
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal

/-! # De Rham Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.DeRhamComplex

noncomputable section

/-!
# IntegralComparison: the actual zeroth-level frame complex is the ordinary residue-field de Rham complex
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k C : Type u) [Field k] [CommRing C] [Algebra k C]

local notation "W" => WittVector p k

attribute [local instance] FormFiniteness.residueAlgebra
  FormFiniteness.ambientAlgebra FormFiniteness.coefficientTower

def residuePDComplex : CochainComplex (ModuleCat.{u} W) ℕ :=
  ((ModuleCat.restrictScalars (WittVector.constantCoeff (p := p) (R := k))).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex k C ⊥ (dividedPowersBot C))

def componentMap (n : ℕ) : ModuleCat.of W (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W C ⊥ (dividedPowersBot C) n) ⟶
    (ModuleCat.restrictScalars (WittVector.constantCoeff (p := p) (R := k))).obj
      (ModuleCat.of k (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form k C ⊥ (dividedPowersBot C) n)) :=
  ModuleCat.ofHom (X := ModuleCat.of W (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W C ⊥ (dividedPowersBot C) n))
    (Y := (ModuleCat.restrictScalars (WittVector.constantCoeff (p := p) (R := k))).obj
      (ModuleCat.of k (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form k C ⊥ (dividedPowersBot C) n)))
    { toFun := PD.FormsBaseQuotientSymbols.formsEquiv W k C (WittVector.constantCoeff_surjective p)
        ⊥ (dividedPowersBot C) n
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := by
        intro r ω
        let e := PD.FormsBaseQuotientSymbols.formsEquiv W k C (WittVector.constantCoeff_surjective p)
          ⊥ (dividedPowersBot C) n
        change e (r • ω) = WittVector.constantCoeff r • e ω
        rw [← IsScalarTower.algebraMap_smul C r ω, map_smul,
          ← IsScalarTower.algebraMap_smul C (WittVector.constantCoeff r) (e ω)]
        rfl }

def componentIso (n : ℕ) : ModuleCat.of W (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W C ⊥ (dividedPowersBot C) n) ≅
    (ModuleCat.restrictScalars (WittVector.constantCoeff (p := p) (R := k))).obj
      (ModuleCat.of k (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form k C ⊥ (dividedPowersBot C) n)) :=
  (LinearEquiv.ofBijective (componentMap p k C n).hom
    (PD.FormsBaseQuotientSymbols.formsEquiv W k C (WittVector.constantCoeff_surjective p)
      ⊥ (dividedPowersBot C) n).bijective).toModuleIso

def pdComplexIso : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex W C ⊥ (dividedPowersBot C) ≅ residuePDComplex p k C :=
  HomologicalComplex.Hom.isoOfComponents
    (componentIso p k C) (by
      intro n m hnm
      change n + 1 = m at hnm
      subst m
      change (componentIso p k C n).hom ≫
        (ModuleCat.restrictScalars (WittVector.constantCoeff (p := p) (R := k))).map
          ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex k C ⊥ (dividedPowersBot C)).d n (n + 1)) =
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex W C ⊥ (dividedPowersBot C)).d n (n + 1) ≫ (componentIso p k C (n + 1)).hom
      rw [PD.BaseQuotientDifferential.complex_d, PD.BaseQuotientDifferential.complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      exact (PD.BaseQuotientDifferential.differential W k C (WittVector.constantCoeff_surjective p)
        ⊥ (dividedPowersBot C) n ω).symm)

def residueComplex : CochainComplex (ModuleCat.{u} W) ℕ :=
  ((ModuleCat.restrictScalars (WittVector.constantCoeff (p := p) (R := k))).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex k C)

def complexIso : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex W C ⊥ (dividedPowersBot C) ≅ residueComplex p k C :=
  pdComplexIso p k C ≪≫
    ((ModuleCat.restrictScalars (WittVector.constantCoeff (p := p) (R := k))).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapIso (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.complexIso k C).symm

def frameComplexIso [Fintype k] [CharP k p] :
    let U := LevelFrame.frame p k C
    letI : Algebra W U.ring := U.base.toAlgebra
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex W U.ring U.ideal U.dividedPowers ≅ residueComplex p k C :=
  complexIso p k C

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.DeRhamComplex
