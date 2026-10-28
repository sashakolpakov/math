import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.TruncatedPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OpenCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.DisjointHypercohomologyNaturality

/-! # Truncated Open Cohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.TruncatedOpenCohomology

noncomputable section

/-! Open restriction identifies the original truncated algebraic hypercohomology and commutes with its inclusion into full cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsOpenImmersion f.left]

def openAlgebraicTruncatedHypercohomologyEquiv (n : ℕ) (r : ℤ) :
    DisjointDerivedHom.complexHypercohomology (TopCat.of X.left)
      (((Sheaves.inverseImage f).mapHomologicalComplex (.up ℤ)).obj (FiltrationExtension.algebraicTruncationComplexInt Y r)) (n : ℤ) ≃ₗ[ℂ]
        FiltrationExtension.algebraicTruncatedCohomology X n r := by
  have h := TruncatedPullback.algebraicTruncatedPullbackInt_isIso f r
  exact Linear.homCongr ℂ (Iso.refl _)
    ((shiftFunctor (DerivedCategory (Sheaves.ComplexSheaves X)) (n : ℤ)).mapIso
      (DerivedCategory.Q.mapIso (@asIso _ _ _ _ (TruncatedPullback.algebraicTruncatedPullbackInt f r) h)))

theorem openAlgebraicTruncatedHypercohomologyEquiv_apply (n : ℕ) (r : ℤ)
    (a : DisjointDerivedHom.complexHypercohomology (TopCat.of X.left)
      (((Sheaves.inverseImage f).mapHomologicalComplex (.up ℤ)).obj (FiltrationExtension.algebraicTruncationComplexInt Y r)) (n : ℤ)) :
    openAlgebraicTruncatedHypercohomologyEquiv f n r a =
      a ≫ (DerivedCategory.Q.map (TruncatedPullback.algebraicTruncatedPullbackInt f r))⟦(n : ℤ)⟧' := by
  change (𝟙 _ ≫ a) ≫ _ = _
  rw [Category.id_comp]
  rfl

theorem openAlgebraicTruncationClass_naturality (n : ℕ) (r : ℤ)
    (a : FiltrationExtension.algebraicTruncatedCohomology Y n r) :
    OpenForms.algebraicDeRhamPullback f n (FiltrationExtension.algebraicTruncationClass Y n r a) =
      FiltrationExtension.algebraicTruncationClass X n r
        (openAlgebraicTruncatedHypercohomologyEquiv f n r
          (DisjointDerivedHom.inverseImageHypercohomologyMap f.left.base (FiltrationExtension.algebraicTruncationComplexInt Y r) (n : ℤ) a)) := by
  erw [← OpenCohomology.openAlgebraicHypercohomologyEquiv_pullback, OpenCohomology.openAlgebraicHypercohomologyEquiv_apply,
    openAlgebraicTruncatedHypercohomologyEquiv_apply]
  let Q := DerivedCategory.Q (C := Sheaves.ComplexSheaves X)
  let S := shiftFunctor (DerivedCategory (Sheaves.ComplexSheaves X)) (n : ℤ)
  let i := ((Sheaves.inverseImage f).mapHomologicalComplex (.up ℤ)).map (FiltrationExtension.algebraicTruncationInclusionInt Y r)
  let j := FiltrationExtension.algebraicTruncationInclusionInt X r
  let p := OpenForms.deRhamSheafPullbackInt f
  let t := TruncatedPullback.algebraicTruncatedPullbackInt f r
  have hs : i ≫ p = t ≫ j := (TruncatedPullback.algebraicTruncatedPullbackInt_inclusion f r).symm
  have hQ := (Q.map_comp i p).symm.trans ((congrArg Q.map hs).trans (Q.map_comp t j))
  have hS := (S.map_comp (Q.map i) (Q.map p)).symm.trans
    ((congrArg S.map hQ).trans (S.map_comp (Q.map t) (Q.map j)))
  change (DisjointDerivedHom.inverseImageHypercohomologyMap f.left.base (Sheaves.algebraicDeRhamSheafComplexInt Y) (n : ℤ)
    (a ≫ (DerivedCategory.Q.map (FiltrationExtension.algebraicTruncationInclusionInt Y r))⟦(n : ℤ)⟧')) ≫ S.map (Q.map p) =
    (DisjointDerivedHom.inverseImageHypercohomologyMap f.left.base (FiltrationExtension.algebraicTruncationComplexInt Y r) (n : ℤ) a ≫
      S.map (Q.map t)) ≫ S.map (Q.map j)
  erw [DisjointHypercohomologyNaturality.inverseImageHypercohomologyMap_postcomp]
  simp only [Category.assoc]
  exact congrArg (fun z => DisjointDerivedHom.inverseImageHypercohomologyMap f.left.base
    (FiltrationExtension.algebraicTruncationComplexInt Y r) (n : ℤ) a ≫ z) hS

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.TruncatedOpenCohomology
