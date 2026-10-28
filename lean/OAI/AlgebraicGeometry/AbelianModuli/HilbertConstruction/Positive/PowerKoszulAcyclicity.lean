import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.KoszulTermIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Addition

/-! # Power Koszul Acyclicity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.PowerKoszulAcyclicity

noncomputable section

/-! If every positive power of a line bundle is acyclic, all terms of a
section Koszul complex for its square with positive-power coefficients are acyclic. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

theorem zariskiCohomology_biprod_subsingleton (M N : X.Modules) (q : ℕ)
    (hM : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H M q))
    (hN : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H N q)) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (M ⊞ N) q) := by
  let F := Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X q
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  have h₁ : IsZero (F.obj M) := @AddCommGrpCat.isZero_of_subsingleton _ hM
  have h₂ : IsZero (F.obj N) := @AddCommGrpCat.isZero_of_subsingleton _ hN
  have hzero : IsZero (F.obj M ⊞ F.obj N) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biprod.hom_ext
    · simpa only [Category.id_comp, zero_comp] using h₁.eq_of_tgt (biprod.fst : F.obj M ⊞ F.obj N ⟶ _) 0
    · simpa only [Category.id_comp, zero_comp] using h₂.eq_of_tgt (biprod.snd : F.obj M ⊞ F.obj N ⟶ _) 0
  exact AddCommGrpCat.subsingleton_of_isZero (hzero.of_iso (F.mapBiprod M N))

theorem lineBundleSquareKoszul_terms_acyclic (G : Line.Bundles.LineBundle X)
    (hG : ∀ b : ℕ, 0 < b → ∀ q : ℕ, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (G.tensorPower b).sheaf (q + 1)))
    (ss : List (Line.Bundles.structureModule X ⟶ (G.tensorPower 2).sheaf))
    (b : ℕ) (hb : 0 < b) (i : ℤ) (q : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
      ((LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex (G.tensorPower 2) (G.tensorPower b).sheaf ss).X i) (q + 1)) := by
  induction ss generalizing b i with
  | nil =>
    by_cases hi : i = 0
    · subst i
      simpa only [LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex, HomologicalComplex.single_obj_X_self] using hG b hb q
    · exact AddCommGrpCat.subsingleton_of_isZero
        ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X (q + 1)).map_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (G.tensorPower b).sheaf i hi))
  | cons s ss ih =>
    let L := G.tensorPower 2
    let C := LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L (G.tensorPower b).sheaf ss
    let F := (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor
    let eM : F.obj (G.tensorPower b).sheaf ≅ (G.tensorPower (2 + b)).sheaf :=
      LineBundle.TensorEquivalence.lineBundleTensorEquivalence_objIso L (G.tensorPower b).sheaf ≪≫ (G.tensorPowerAddIso 2 b).symm
    let eT : F.obj (C.X i) ≅
        (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L (G.tensorPower (2 + b)).sheaf ss).X i :=
      LineBundle.KoszulTermIsomorphisms.lineBundleKoszul_tensorTermIso L (G.tensorPower b).sheaf ss i ≪≫
        LineBundle.KoszulTermIsomorphisms.lineBundleKoszul_coefficientTermIso L eM ss i
    have hT : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (F.obj (C.X i)) (q + 1)) := by
      have : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
          ((LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L (G.tensorPower (2 + b)).sheaf ss).X i) (q + 1)) :=
        ih (2 + b) (by omega) i
      exact (ConcreteCategory.bijective_of_isIso
        ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X (q + 1)).map eT.hom)).injective.subsingleton
    have hsum := zariskiCohomology_biprod_subsingleton (C.X (i + 1)) (F.obj (C.X i))
      (q + 1) (ih b hb (i + 1)) hT
    have := hsum
    exact (ConcreteCategory.bijective_of_isIso
      ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X (q + 1)).map
        (LineBundle.KoszulTermIsomorphisms.lineBundleSectionKoszulStep_XIsoBiprod L s C i).hom)).injective.subsingleton

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.PowerKoszulAcyclicity
