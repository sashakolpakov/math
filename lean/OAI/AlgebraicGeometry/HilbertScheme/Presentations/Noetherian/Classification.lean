import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialParameterUniqueness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyDescentUniqueness

/-! # Classification -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.Classification.GradedHilbert

noncomputable section

/-! The actual affine Hilbert parameters glue to classify canonical
polynomial families over every locally noetherian test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {T : Over S} [IsLocallyNoetherian T.left]

theorem existsUnique_noetherian_scheme_hilbert_parameter
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) (P : Polynomial ℚ)
    (hP : CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃! x : T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  let C := T.left.affineOpenCover
  let U (i : C.I₀) : Over S := Over.mk (C.f i ≫ T.hom)
  let b (i : C.I₀) : U i ⟶ T := Over.homMk (C.f i) rfl
  let H := BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)
  let V := BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)
  let : ∀ i, IsNoetherianRing (C.X i) := fun i => isLocallyNoetherian_Spec.mp
    (isLocallyNoetherian_of_isOpenImmersion (C.f i))
  have hex (i : C.I₀) : ∃ x : U i ⟶ H,
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x V =
        Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b i) F := by
    have hR : IsNoetherianRing (C.X i) := isLocallyNoetherian_Spec.mp
      (isLocallyNoetherian_of_isOpenImmersion (C.f i))
    exact (@AffineClassification.GradedHilbert.existsUnique_noetherian_affine_hilbert_parameter (C.X i) _ hR S _ n N ι _ _ (C.f i ≫ T.hom)
      (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b i) F) P
      ((hP.pullback (b i)).affine_residue) hN hr).exists
  choose x hx using hex
  have hc (i j : C.I₀) : pullback.fst (C.f i) (C.f j) ≫ (x i).left =
      pullback.snd (C.f i) (C.f j) ≫ (x j).left := by
    let W : Over S := Over.mk (pullback.fst (C.f i) (C.f j) ≫ C.f i ≫ T.hom)
    let c : W ⟶ U i := Over.homMk (pullback.fst (C.f i) (C.f j)) rfl
    let d : W ⟶ U j := Over.homMk (pullback.snd (C.f i) (C.f j))
      (pullback.condition_assoc T.hom).symm
    let : IsLocallyNoetherian W.left := inferInstanceAs
      (IsLocallyNoetherian (pullback (C.f i) (C.f j)))
    have hcd : c ≫ b i = d ≫ b j := Over.OverMorphism.ext (pullback.condition)
    have hi : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (c ≫ x i) V =
        Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (c ≫ b i) F := by
      rw [Hilbert.Functor.pullbackFamily_comp, hx, Hilbert.Functor.pullbackFamily_comp]
    have hj : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (d ≫ x j) V =
        Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (c ≫ b i) F := by
      rw [hcd, Hilbert.Functor.pullbackFamily_comp, hx, Hilbert.Functor.pullbackFamily_comp]
    exact congrArg Over.Hom.left (PolynomialParameterUniqueness.GradedHilbert.noetherian_polynomial_hilbert_parameter_unique
      (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (c ≫ b i) F) P
      (hP.pullback (c ≫ b i)) hN hr (c ≫ x i) (d ≫ x j) hi hj)
  let z : T.left ⟶ H.left := C.openCover.glueMorphisms (fun i => (x i).left) hc
  have hw : z ≫ H.hom = T.hom := by
    apply C.openCover.hom_ext
    intro i
    rw [← Category.assoc]
    exact (congrArg (fun a => a ≫ H.hom)
      (C.openCover.ι_glueMorphisms (fun i => (x i).left) hc i)).trans (x i).w
  let y : T ⟶ H := Over.homMk z hw
  have hyi (i : C.I₀) : b i ≫ y = x i :=
    Over.OverMorphism.ext (C.openCover.ι_glueMorphisms (fun i => (x i).left) hc i)
  have hy : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) y V = F := by
    let : ∀ i, IsOpenImmersion (b i).left := fun i => inferInstanceAs (IsOpenImmersion (C.f i))
    apply Hilbert.FamilyDescentUniqueness.family_eq_of_openCover (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) U b
      (fun t => C.openCover.exists_eq t)
    intro i
    rw [← Hilbert.Functor.pullbackFamily_comp, hyi]
    exact hx i
  exact ⟨y, hy, fun k hk => PolynomialParameterUniqueness.GradedHilbert.noetherian_polynomial_hilbert_parameter_unique F P hP hN hr k y hk hy⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.Classification.GradedHilbert
