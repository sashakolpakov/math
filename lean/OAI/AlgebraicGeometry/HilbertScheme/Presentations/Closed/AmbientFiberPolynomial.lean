import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientProjectivePresentation

/-! # Ambient Fiber Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientFiberPolynomial.Core

noncomputable section

/-! Inclusion in a closed projective ambient scheme preserves exactly
the statement's field-fiber Hilbert-polynomial predicate, including its
arbitrary Cartesian coordinate comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y : Over S} (j : X ⟶ Y) [IsClosedImmersion j.left]
variable (B : Has.Core.ProjectivePresentation Y) {T : Over S} (F : Hilbert.Functor.Family X T) (P : Polynomial ℚ)

theorem hasFiberHilbertPolynomial_of_pushforward
    (h : Has.Core.HasFiberHilbertPolynomial B (Hilbert.ClosedAmbientMap.pushforwardFamily j F) P) :
    Has.Core.HasFiberHilbertPolynomial (B.precompose j) F P := by
  intro K _ a
  let t : Over S := Over.mk (a ≫ T.hom)
  let b : t ⟶ T := Over.homMk a rfl
  let J := Hilbert.Functor.pullbackFamily X b F
  let e := AmbientProjectivePresentation.Hilbert.closedAmbientSubschemeIso j J
  have hh := h K a
  dsimp only at hh ⊢
  rw [← Hilbert.ClosedAmbientNaturality.pushforwardFamily_baseChange] at hh
  obtain ⟨q, f, hq, hf, hinc, hproj, hP⟩ := hh
  let g : (Hilbert.ClosedAmbientMap.pushforwardFamily j J).val.subscheme ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading K B.dimension) := f
  let : IsClosedImmersion g := hf
  have hgi : g ≫ q = (Hilbert.ClosedAmbientMap.pushforwardFamily j J).val.subschemeι ≫
      (prod.snd : t ⨯ Y ⟶ Y).left ≫ B.embedding := hinc
  have hgp : g ≫ Has.Core.projectiveSpaceMap K B.dimension =
      Hilbert.Functor.familyProjection Y (Hilbert.ClosedAmbientMap.pushforwardFamily j J).val := hproj
  have hc : IsClosedImmersion (e.hom ≫ g) := inferInstance
  refine ⟨q, e.hom ≫ g, hq, hc, ?_, ?_, ?_⟩
  · exact (Category.assoc e.hom g q).trans
      ((congrArg (fun z => e.hom ≫ z) hgi).trans
        (AmbientProjectivePresentation.Hilbert.closedAmbientSubschemeIso_hom_projective j J B))
  · exact (Category.assoc e.hom g _).trans
      ((congrArg (fun z => e.hom ≫ z) hgp).trans
        (AmbientProjectivePresentation.Hilbert.closedAmbientSubschemeIso_hom_projection j J))
  · have hk := Scheme.Hom.ker_comp_of_isIso e.hom g
    exact (congrArg (fun I => Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I).toIdeal P) hk).mpr hP

theorem hasFiberHilbertPolynomial_pushforward
    (h : Has.Core.HasFiberHilbertPolynomial (B.precompose j) F P) :
    Has.Core.HasFiberHilbertPolynomial B (Hilbert.ClosedAmbientMap.pushforwardFamily j F) P := by
  intro K _ a
  let t : Over S := Over.mk (a ≫ T.hom)
  let b : t ⟶ T := Over.homMk a rfl
  let J := Hilbert.Functor.pullbackFamily X b F
  let e := AmbientProjectivePresentation.Hilbert.closedAmbientSubschemeIso j J
  have hh := h K a
  dsimp only at hh ⊢
  rw [← Hilbert.ClosedAmbientNaturality.pushforwardFamily_baseChange]
  obtain ⟨q, f, hq, hf, hinc, hproj, hP⟩ := hh
  let g : J.val.subscheme ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading K B.dimension) := f
  let : IsClosedImmersion g := hf
  have hgi : g ≫ q = J.val.subschemeι ≫
      (prod.snd : t ⨯ X ⟶ X).left ≫ (B.precompose j).embedding := hinc
  have hgp : g ≫ Has.Core.projectiveSpaceMap K B.dimension = Hilbert.Functor.familyProjection X J.val := hproj
  have hc : IsClosedImmersion (e.inv ≫ g) := inferInstance
  refine ⟨q, e.inv ≫ g, hq, hc, ?_, ?_, ?_⟩
  · exact (Category.assoc e.inv g q).trans
      ((congrArg (fun z => e.inv ≫ z) hgi).trans
        ((Iso.inv_comp_eq e).mpr (AmbientProjectivePresentation.Hilbert.closedAmbientSubschemeIso_hom_projective j J B).symm))
  · exact (Category.assoc e.inv g _).trans
      ((congrArg (fun z => e.inv ≫ z) hgp).trans
        ((Iso.inv_comp_eq e).mpr (AmbientProjectivePresentation.Hilbert.closedAmbientSubschemeIso_hom_projection j J).symm))
  · have hk := Scheme.Hom.ker_comp_of_isIso e.inv g
    exact (congrArg (fun I => Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I).toIdeal P) hk).mpr hP

theorem hasFiberHilbertPolynomial_pushforward_iff :
    Has.Core.HasFiberHilbertPolynomial B (Hilbert.ClosedAmbientMap.pushforwardFamily j F) P ↔
      Has.Core.HasFiberHilbertPolynomial (B.precompose j) F P :=
  ⟨hasFiberHilbertPolynomial_of_pushforward j B F P,
    hasFiberHilbertPolynomial_pushforward j B F P⟩

theorem hasFiberHilbertPolynomial_closedAmbient_iff
    {X : Over S} (BX : Has.Core.ProjectivePresentation X) {T : Over S}
    (F : Hilbert.Functor.Family X T) (P : Polynomial ℚ) :
    Has.Core.HasFiberHilbertPolynomial (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S BX.dimension)
      (Hilbert.ClosedAmbientMap.pushforwardFamily BX.closedAmbientEmbedding F) P ↔ Has.Core.HasFiberHilbertPolynomial BX F P := by
  have h := hasFiberHilbertPolynomial_pushforward_iff BX.closedAmbientEmbedding
    (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S BX.dimension) F P
  rwa [Has.Core.ProjectivePresentation.canonical_precompose] at h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientFiberPolynomial.Core
