import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryPolynomialParameterUniqueness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyDescentUniqueness

/-! # Parameter Open Cover Gluing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ParameterOpenCoverGluing.GradedHilbert

noncomputable section

/-! Compatible actual Hilbert parameters glue over arbitrary open covers
of arbitrary test schemes. Compatibility follows from family uniqueness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {T : Over S}

theorem hilbert_parameter_of_openCover
    (F : Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) (P : Polynomial ℚ)
    (hP : CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    {κ : Type u} (U : κ → Over S) (b : ∀ i, U i ⟶ T)
    [∀ i, IsOpenImmersion (b i).left]
    (hcover : ∀ t : T.left, ∃ i, ∃ y : (U i).left, (b i).left y = t)
    (h : ∀ i, ∃ x : U i ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) =
      Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b i) F) :
    ∃! x : T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  let C := FamilyLocality.testOpenCover U b hcover
  let H := BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)
  let V := BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)
  choose x hx using h
  have hc (i j : κ) : pullback.fst (b i).left (b j).left ≫ (x i).left =
      pullback.snd (b i).left (b j).left ≫ (x j).left := by
    let W : Over S := Over.mk (pullback.fst (b i).left (b j).left ≫ (b i).left ≫ T.hom)
    let c : W ⟶ U i := Over.homMk (pullback.fst (b i).left (b j).left) (by
      change _ ≫ (U i).hom = _ ≫ (b i).left ≫ T.hom
      rw [(b i).w])
    let d : W ⟶ U j := Over.homMk (pullback.snd (b i).left (b j).left) (by
      change _ ≫ (U j).hom = _ ≫ (b i).left ≫ T.hom
      rw [← (b j).w]
      exact (pullback.condition_assoc T.hom).symm)
    have hcd : c ≫ b i = d ≫ b j := Over.OverMorphism.ext (pullback.condition)
    have hi : Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (c ≫ x i) V =
        Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (c ≫ b i) F := by
      rw [Functor.pullbackFamily_comp, hx, Functor.pullbackFamily_comp]
    have hj : Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (d ≫ x j) V =
        Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (c ≫ b i) F := by
      rw [hcd, Functor.pullbackFamily_comp, hx, Functor.pullbackFamily_comp]
    exact congrArg Over.Hom.left (ArbitraryPolynomialParameterUniqueness.GradedHilbert.polynomial_hilbert_parameter_unique
      (Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (c ≫ b i) F) P
      (hP.pullback (c ≫ b i)) hN hr (c ≫ x i) (d ≫ x j) hi hj)
  let z : T.left ⟶ H.left := C.glueMorphisms (fun i => (x i).left) hc
  have hw : z ≫ H.hom = T.hom := by
    apply C.hom_ext
    intro i
    rw [← Category.assoc]
    exact (congrArg (fun a => a ≫ H.hom) (C.ι_glueMorphisms (fun i => (x i).left) hc i)).trans
      ((x i).w.trans (b i).w.symm)
  let y : T ⟶ H := Over.homMk z hw
  have hyi (i : κ) : b i ≫ y = x i := Over.OverMorphism.ext (C.ι_glueMorphisms (fun i => (x i).left) hc i)
  have hy : Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) y V = F := by
    apply FamilyDescentUniqueness.family_eq_of_openCover (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) U b hcover
    intro i
    rw [← Functor.pullbackFamily_comp, hyi]
    exact hx i
  exact ⟨y, hy, fun k hk => ArbitraryPolynomialParameterUniqueness.GradedHilbert.polynomial_hilbert_parameter_unique F P hP hN hr k y hk hy⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ParameterOpenCoverGluing.GradedHilbert
