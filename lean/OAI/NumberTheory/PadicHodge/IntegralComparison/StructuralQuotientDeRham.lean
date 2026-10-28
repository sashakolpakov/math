import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.DeRhamComplex

/-! # Structural Quotient De Rham -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.StructuralQuotientDeRham

noncomputable section

/-! Base-ideal reduction of the original complex with its exact structural algebra action. -/

open _root_.CategoryTheory

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A] [LinearOrder σ]
  (I : Ideal R) (J : Ideal A) (hJ : J = I.map (algebraMap R A))
  (x : σ → A) (b : Module.Basis σ A (KaehlerDifferential R A))
  (hb : ∀ i, b i = KaehlerDifferential.D R A (x i))

include σ hJ x b hb in
theorem exists_iso :
    let : Algebra R (A ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra
    ∃ e : IntegralComparison.Module.IdealQuotient.complex R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A) ≅
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (A ⧸ J),
    ∀ (m : ℕ) (a : A) (v : Fin m → A),
      ((IntegralComparison.Module.IdealQuotient.complexProjection R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A)) ≫ e.hom).f m
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (A ⧸ J)
          (Ideal.Quotient.mk J a) (fun i => Ideal.Quotient.mk J (v i)) := by
  have he : ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra =
      (inferInstance : Algebra R (A ⧸ J)) := Algebra.algebra_ext _ _ (fun _ => rfl)
  rw [he]
  subst J
  refine ⟨IntegralComparison.Quotient.DeRhamComplex.iso R A σ I x b hb, ?_⟩
  intro m a v
  exact (IntegralComparison.Quotient.DeRhamComplex.projection_iso_apply R A σ I x b hb m
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)).trans
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol (CommAlgCat.ofHom
        (IsScalarTower.toAlgHom R A (A ⧸ I.map (algebraMap R A)))) m a v)

def iso :
    let : Algebra R (A ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra
    IntegralComparison.Module.IdealQuotient.complex R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A) ≅
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (A ⧸ J) :=
  (exists_iso R A σ I J hJ x b hb).choose

theorem projection_iso_symbol (m : ℕ) (a : A) (v : Fin m → A) :
    let : Algebra R (A ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra
    ((IntegralComparison.Module.IdealQuotient.complexProjection R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A)) ≫
      (iso R A σ I J hJ x b hb).hom).f m (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
        AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (A ⧸ J) (Ideal.Quotient.mk J a)
          (fun i => Ideal.Quotient.mk J (v i)) :=
  (exists_iso R A σ I J hJ x b hb).choose_spec m a v

theorem projection_iso_apply (m : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A m) :
    let : Algebra R (A ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra
    ((IntegralComparison.Module.IdealQuotient.complexProjection R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A)) ≫
      (iso R A σ I J hJ x b hb).hom).f m ω =
        AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom
          (show A →ₐ[R] A ⧸ J from { toRingHom := Ideal.Quotient.mk J, commutes' := fun _ => rfl })) m ω := by
  let : Algebra R (A ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap R A)).toAlgebra
  let g :=
    ((IntegralComparison.Module.IdealQuotient.complexProjection R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A) ≫
      (iso R A σ I J hJ x b hb).hom).f m).hom
  change g ω = _
  obtain ⟨t, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A m).mkQ_surjective ω
  induction t using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    exact g.map_zero
  | add t s ht hs =>
    simp only [map_add]
    exact (g.map_add _ _).trans (congrArg₂ (· + ·) ht hs)
  | single v a =>
    exact (projection_iso_symbol R A σ I J hJ x b hb m a v).trans
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol (CommAlgCat.ofHom
        (show A →ₐ[R] A ⧸ J from { toRingHom := Ideal.Quotient.mk J, commutes' := fun _ => rfl })) m a v).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.StructuralQuotientDeRham
