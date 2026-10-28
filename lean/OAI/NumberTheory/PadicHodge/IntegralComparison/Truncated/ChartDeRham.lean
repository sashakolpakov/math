import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.StandardEtaleLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.SurjectiveBase

/-! # Chart De Rham -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.ChartDeRham

noncomputable section

/-! The ordinary de Rham complex of an actual finite-Witt-level
coordinate chart is the de Rham complex of its genuine crystalline
frame. The comparison preserves the canonical differential symbols. -/

open _root_.CategoryTheory

namespace PrincipalBaseComplex

universe u

theorem ofIdealEq_symbol (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (r : R) (δR : DividedPowers (Ideal.span {r})) (I : Ideal A) (δ : DividedPowers I)
    (hI : I = Ideal.span {algebraMap R A r})
    (hf : DividedPowers.IsDPMorphism δR δ (algebraMap R A))
    (m : ℕ) (a : A) (v : Fin m → A) :
    ((Principal.BaseComplex.ofIdealEq R A r δR I δ hI hf).hom.f m) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v := by
  subst I
  exact Principal.BaseForms.formsEquiv_symbol R A r δR δ hf m a v

end PrincipalBaseComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (σ : Type u) [Finite σ] (A : Type u) [CommRing A]
  [Algebra (Witt.Ring p k n) A]
  [Algebra (MvPolynomial σ (Witt.Ring p k n)) A]
  [IsScalarTower (Witt.Ring p k n)
    (MvPolynomial σ (Witt.Ring p k n)) A]
  (P : StandardEtalePresentation (MvPolynomial σ (Witt.Ring p k n)) A)

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.StandardEtaleLift.Ring p k n σ A P
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.Ring p L n
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.ideal p L n
local notation "δ" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.dividedPowers p k L n

@[instance_reducible] def sourceWittAlgebra : Algebra W A :=
  ((algebraMap S A).comp (Witt.quotient p k n)).toAlgebra

local instance frameWittAlgebra : Algebra W T := (SmoothWitt.FrameRing.base p k L n).toAlgebra

def quotientAlgEquiv : letI := sourceWittAlgebra p k n A; T ≃ₐ[W] A := by
  letI := sourceWittAlgebra p k n A
  exact {
    __ := StandardEtaleLift.quotientEquiv p k n σ A P
    commutes' := fun w =>
      (StandardEtaleLift.quotientEquiv_mk p k n σ A P (algebraMap W L w)).trans
        (StandardEtaleLift.reduction_base p k n σ A P w) }

def iso : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex W T I δ ≅
    ((ModuleCat.restrictScalars (algebraMap W S)).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex S A) := by
  letI := sourceWittAlgebra p k n A
  letI : IsScalarTower W S A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact SmoothWitt.FrameComplex.iso p k L n ≪≫
    (OrdinaryDeRhamFunctor.Ordinary.functor W).mapIso
      (CommAlgCat.isoMk (quotientAlgEquiv p k n σ A P)) ≪≫
        GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.iso W S A Ideal.Quotient.mk_surjective

omit [Fintype k] in
theorem iso_symbol (m : ℕ) (a : T) (v : Fin m → T) :
    ((iso p k n σ A P).hom.f m) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W T I δ a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S A (quotientAlgEquiv p k n σ A P a)
        (fun i => quotientAlgEquiv p k n σ A P (v i)) := by
  let := sourceWittAlgebra p k n A
  let : IsScalarTower W S A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  change OrdinaryBaseQuotient.Ordinary.formsEquiv W S A Ideal.Quotient.mk_surjective m
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.isoMk (quotientAlgEquiv p k n σ A P)).hom m
      (((SmoothWitt.FrameComplex.iso p k L n).hom.f m) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W T I δ a v))) = _
  have hp := PrincipalBaseComplex.ofIdealEq_symbol W T (p : W)
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) I δ (SmoothWitt.FrameComplex.ideal_eq p k L n)
    (SmoothWitt.FrameRing.base_isDPMorphism p k L n) m a v
  exact (congrArg (fun ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W T m =>
    OrdinaryBaseQuotient.Ordinary.formsEquiv W S A Ideal.Quotient.mk_surjective m
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.isoMk (quotientAlgEquiv p k n σ A P)).hom m ω)) hp).trans
    ((congrArg (OrdinaryBaseQuotient.Ordinary.formsEquiv W S A Ideal.Quotient.mk_surjective m)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol (CommAlgCat.isoMk (quotientAlgEquiv p k n σ A P)).hom m a v)).trans
        (OrdinaryBaseQuotient.Ordinary.formsEquiv_symbol W S A Ideal.Quotient.mk_surjective m
          (quotientAlgEquiv p k n σ A P a) (fun i => quotientAlgEquiv p k n σ A P (v i))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.ChartDeRham
