import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CanonicalChartSections

/-! # Pullback Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.PullbackValues

noncomputable section

/-! Regular coordinate functions pull back along the constructed projective chart map to its supplied coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {T : Scheme.{u}} {n : ℕ}

theorem projectiveAway_section_pullback (i : Fin (n + 1))
    (h : ⊤ ≤ Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one ⁻¹ᵁ
        Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)) :
    Proj.awayToSection (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i) ≫
      (Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one).appLE
          (Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)) ⊤ h =
      (Scheme.ΓSpecIso (CommRingCat.of (Evaluation.projectiveChartRing R n i))).inv := by
  let U := Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
  let e := Proj.basicOpenIsoSpec (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one
  have he : e.hom.appTop = (Scheme.ΓSpecIso _).hom ≫
      Proj.awayToSection (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i) ≫ U.topIso.inv :=
    Proj.basicOpenToSpec_app_top _ _
  have hi : (Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one).appLE U ⊤ h =
        U.topIso.inv ≫ e.inv.appTop :=
    (Scheme.Hom.appLE_comp_appLE e.inv U.ι U ⊤ ⊤ U.ι_preimage_self.ge le_rfl).symm
  rw [← Iso.inv_comp_eq] at he
  rw [hi, ← Category.assoc, ← he, Category.assoc, ← Scheme.Hom.comp_appTop,
    Iso.inv_hom_id, Scheme.Hom.id_appTop, Category.comp_id]

theorem projectiveChartMap_section_pullback (c : R →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1)
    (h : ⊤ ≤ Evaluation.projectiveChartMap c v i hi ⁻¹ᵁ
      Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)) :
    Proj.awayToSection (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i) ≫
      (Evaluation.projectiveChartMap c v i hi).appLE
        (Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)) ⊤ h =
      CommRingCat.ofHom (Evaluation.projectiveChartEvaluation c v i hi) := by
  let a := Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one
  let U := Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
  have ha : ⊤ ≤ a ⁻¹ᵁ U := by
    dsimp [a, U]
    rw [← Proj.opensRange_awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one, Scheme.Hom.preimage_opensRange]
  let e := CommRingCat.ofHom (Evaluation.projectiveChartEvaluation c v i hi)
  have hsa : ⊤ ≤ (Spec.map e ≫ a) ⁻¹ᵁ U := by
    change ⊤ ≤ Spec.map e ⁻¹ᵁ (a ⁻¹ᵁ U)
    rw [top_le_iff.mp ha]
    exact le_rfl
  have h1 := Scheme.Hom.appLE_comp_appLE (Spec.map e) a U ⊤ ⊤ ha le_rfl
  have h2 := Scheme.Hom.appLE_comp_appLE T.toSpecΓ (Spec.map e ≫ a) U ⊤ ⊤ hsa le_rfl
  change Proj.awayToSection (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i) ≫
    (T.toSpecΓ ≫ Spec.map e ≫ a).appLE U ⊤ h = e
  rw [← h2, ← Category.assoc, ← h1, ← Category.assoc,
    projectiveAway_section_pullback i ha]
  have ht (X Y : Scheme.{u}) (f : X ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) :
      f.appLE ⊤ ⊤ h = f.appTop := f.appLE_eq_app
  have hn : ((Scheme.ΓSpecIso (CommRingCat.of (Evaluation.projectiveChartRing R n i))).inv ≫
      (Spec.map e).appTop) ≫ T.toSpecΓ.appTop = e := by
    rw [← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Scheme.toSpecΓ_appTop,
      ]
    exact (congrArg (fun z => e ≫ z) (Scheme.ΓSpecIso Γ(T, ⊤)).inv_hom_id).trans
      (Category.comp_id e)
  exact (congrArg₂ (fun x y =>
      ((Scheme.ΓSpecIso (CommRingCat.of (Evaluation.projectiveChartRing R n i))).inv ≫ x) ≫ y)
    (ht _ _ (Spec.map e) le_rfl) (ht _ _ T.toSpecΓ le_rfl)).trans hn

theorem projectiveChartMap_coordinate_pullback (c : R →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1)
    (h : ⊤ ≤ Evaluation.projectiveChartMap c v i hi ⁻¹ᵁ
      Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)) (j : Fin (n + 1)) :
    (Evaluation.projectiveChartMap c v i hi).appLE
      (Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)) ⊤ h
      (Proj.awayToSection (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
        (HomogeneousLocalization.Away.mk (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.isHomogeneous_X R i)
          1 (MvPolynomial.X j) (by
            change (MvPolynomial.X j : Projective.ProjectivePresentations.coordinateRing R n).IsHomogeneous 1
            exact MvPolynomial.isHomogeneous_X R j))) =
      v j :=
  (ConcreteCategory.congr_hom (projectiveChartMap_section_pullback c v i hi h) _).trans
    (Evaluation.projectiveChartEvaluation_coordinate c v i hi j)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.PullbackValues
