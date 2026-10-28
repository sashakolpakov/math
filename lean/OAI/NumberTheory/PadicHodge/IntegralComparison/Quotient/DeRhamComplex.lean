import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormsExactness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient

/-! # De Rham Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.DeRhamComplex

noncomputable section

/-! Reducing the actual ordinary de Rham complex by a base ideal commutes with its differential. -/

open _root_.CategoryTheory

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A] [LinearOrder σ]
  (I : Ideal R) (x : σ → A) (b : Module.Basis σ A (KaehlerDifferential R A))
  (hb : ∀ i, b i = KaehlerDifferential.D R A (x i))

local notation "B" => A ⧸ I.map (algebraMap R A)
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B

def componentIso (m : ℕ) : (IntegralComparison.Module.IdealQuotient.complex R I K).X m ≅ (L).X m :=
  (FormsExactness.scalarEquiv R A σ I x b hb m).toModuleIso

theorem differential (m : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A m) :
    FormsExactness.scalarEquiv R A σ I x b hb (m + 1)
      (Submodule.Quotient.mk (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A m ω)) =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R B m
      (FormsExactness.scalarEquiv R A σ I x b hb m (Submodule.Quotient.mk ω)) := by
  rw [FormsExactness.scalarEquiv_mk, FormsExactness.scalarEquiv_mk]
  exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_differential (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) m ω

def iso : IntegralComparison.Module.IdealQuotient.complex R I K ≅ L :=
  HomologicalComplex.Hom.isoOfComponents (componentIso R A σ I x b hb) (by
    intro m q hmq
    change m + 1 = q at hmq
    subst q
    change (componentIso R A σ I x b hb m).hom ≫ (L).d m (m + 1) =
      (IntegralComparison.Module.IdealQuotient.functor R I).map ((K).d m (m + 1)) ≫
        (componentIso R A σ I x b hb (m + 1)).hom
    dsimp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    obtain ⟨t, rfl⟩ := (I • ⊤ : Submodule R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A m)).mkQ_surjective ω
    exact (differential R A σ I x b hb m t).symm)

theorem projection_iso_apply (m : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A m) :
    ((IntegralComparison.Module.IdealQuotient.complexProjection R I K) ≫ (iso R A σ I x b hb).hom).f m ω =
      OrdinaryFormScalars.Ordinary.map R A B m ω :=
  FormsExactness.scalarEquiv_mk R A σ I x b hb m ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.DeRhamComplex
