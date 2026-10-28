import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseQuotient

/-! # Forms Base Quotient Symbols -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseQuotientSymbols

noncomputable section

/-!
# IntegralComparison: quotient-base comparison of actual PD forms preserves the canonical symbols
-/

universe u

section Relations

variable (A : Type u) [CommRing A] (I : Ideal A) (δ : DividedPowers I) (n : ℕ)

def relation (P : Submodule A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n)) (r : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.RelationIndex A I n) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n ⧸ P :=
  P.mkQ (Finsupp.single (Function.update r.v r.i (δ.dpow (r.m + 1) r.x)) 1) -
    P.mkQ (Finsupp.single (Function.update r.v r.i r.x) (δ.dpow r.m r.x))

def relations (P : Submodule A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n)) : Submodule A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n ⧸ P) :=
  Submodule.span A (Set.range (relation A I δ n P))

abbrev Quotient (P : Submodule A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n)) :=
  (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n ⧸ P) ⧸ relations A I δ n P

def rawSymbol (P : Submodule A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n)) (a : A) (v : Fin n → A) : Quotient A I δ n P :=
  (relations A I δ n P).mkQ (P.mkQ (Finsupp.single v a))

def transport (P Q : Submodule A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n)) (h : P = Q) :
    Quotient A I δ n P ≃ₗ[A] Quotient A I δ n Q := by
  subst Q
  exact LinearEquiv.refl _ _

theorem transport_symbol (P Q : Submodule A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A n)) (h : P = Q)
    (a : A) (v : Fin n → A) :
    transport A I δ n P Q h (rawSymbol A I δ n P a v) = rawSymbol A I δ n Q a v := by
  subst Q
  rfl

end Relations

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  (h : Function.Surjective (algebraMap R S)) (I : Ideal A) (δ : DividedPowers I)

def formsEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n ≃ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form S A I δ n :=
  transport A I δ n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations S A n)
    (FormsBaseQuotient.ordinaryRelations_eq R S A h n)

theorem formsEquiv_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formsEquiv R S A h I δ n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ a v) = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol S A I δ a v :=
  transport_symbol A I δ n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations S A n)
    (FormsBaseQuotient.ordinaryRelations_eq R S A h n) a v

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseQuotientSymbols
