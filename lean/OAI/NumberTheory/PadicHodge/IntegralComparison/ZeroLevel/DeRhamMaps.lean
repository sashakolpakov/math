import OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.IdealDeRhamNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.DeRhamComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.BaseQuotientNaturality

/-! # De Rham Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.DeRhamMaps

noncomputable section

/-!
# IntegralComparison: the actual Witt-to-residue de Rham comparison respects chart maps
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k C D : Type u) [Field k] [CommRing C] [CommRing D]
  [Algebra k C] [Algebra k D] (f : C →ₐ[k] D)

local notation "W" => WittVector p k

attribute [local instance] FormFiniteness.residueAlgebra
  FormFiniteness.ambientAlgebra FormFiniteness.coefficientTower

def pdMap : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex W C ⊥ (dividedPowersBot C) ⟶
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex W D ⊥ (dividedPowersBot D) :=
  PD.DeRhamComplexMap.map (CommAlgCat.ofHom (f.restrictScalars W))
    (Zero.IdealPDMap.map (dividedPowersBot D) f.toRingHom).isDPMorphism

def residueMap : DeRhamComplex.residueComplex p k C ⟶
    DeRhamComplex.residueComplex p k D :=
  ((ModuleCat.restrictScalars (WittVector.constantCoeff (p := p) (R := k))).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (OrdinaryDeRhamFunctor.Ordinary.map (CommAlgCat.ofHom f))

theorem forms (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W C ⊥ (dividedPowersBot C) n) :
    AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv k D n
      (PD.FormsBaseQuotientSymbols.formsEquiv W k D (WittVector.constantCoeff_surjective p)
        ⊥ (dividedPowersBot D) n
          (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (f.restrictScalars W))
            (Zero.IdealPDMap.map (dividedPowersBot D) f.toRingHom).isDPMorphism n ω)) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom f) n
        (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv k C n
          (PD.FormsBaseQuotientSymbols.formsEquiv W k C (WittVector.constantCoeff_surjective p)
            ⊥ (dividedPowersBot C) n ω)) := by
  have h := PD.BaseQuotientNaturality.naturality W k C D (WittVector.constantCoeff_surjective p)
    ⊥ (dividedPowersBot C) ⊥ (dividedPowersBot D) f
      (Zero.IdealPDMap.map (dividedPowersBot D) f.toRingHom).isDPMorphism n ω
  exact (congrArg (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv k D n) h).trans
    (Zero.IdealDeRhamNaturality.forms (CommAlgCat.ofHom f)
      (Zero.IdealPDMap.map (dividedPowersBot D) f.toRingHom).isDPMorphism n _)

theorem complexes : pdMap p k C D f ≫ (DeRhamComplex.complexIso p k D).hom =
    (DeRhamComplex.complexIso p k C).hom ≫ residueMap p k C D f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact forms p k C D f n ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.DeRhamMaps
