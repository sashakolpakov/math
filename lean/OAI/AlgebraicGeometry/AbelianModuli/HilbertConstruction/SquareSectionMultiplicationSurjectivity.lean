import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SquareKoszulSectionSurjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulTopTensorPower
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulPreviousPowerCopies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.RetractSectionFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.MapSectionFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MultiplicationProduct

/-! # Square Section Multiplication Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SquareSectionMultiplicationSurjectivity

noncomputable section

/-! A covering square-section Koszul complex forces high-power sections
to be sums of products of square sections and sections two degrees lower. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators
universe u

theorem lineBundleSquare_powerSections_products
    {X : Scheme.{u}} (G : Line.Bundles.LineBundle X)
    (hG : ∀ b : ℕ, 0 < b → ∀ q : ℕ, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (G.tensorPower b).sheaf (q + 1)))
    (ss : List (Line.Bundles.structureModule X ⟶ (G.tensorPower 2).sheaf))
    (hcover : ∀ x : X, ∃ s ∈ ss, x ∈ Ample.LineBundles.sectionNonvanishing s) (hss : 0 < ss.length)
    (b : ℕ) (hb : 0 < b) :
    ∀ t : Line.Bundles.structureModule X ⟶ (G.tensorPower (2 + ((ss.length - 1) * 2 + b))).sheaf,
      ∃ (n : ℕ) (s : Fin n → (Line.Bundles.structureModule X ⟶ (G.tensorPower 2).sheaf))
        (v : Fin n → (Line.Bundles.structureModule X ⟶ (G.tensorPower ((ss.length - 1) * 2 + b)).sheaf)),
        t = ∑ i, Tensor.ProductSections.tensorProductSection (s i) (v i) ≫
          (G.tensorPowerAddIso 2 ((ss.length - 1) * 2 + b)).inv := by
  let q := (ss.length - 1) * 2 + b
  let K := LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex (G.tensorPower 2) (G.tensorPower b).sheaf ss
  have heq : ss.length * 2 + b = 2 + q := by dsimp [q]; omega
  let e : K.X 0 ≅ (G.tensorPower (2 + q)).sheaf :=
    KoszulTopTensorPower.lineBundleSquareKoszulTopPowerIso G ss b ≪≫
      eqToIso (congrArg (fun n => (G.tensorPower n).sheaf) heq)
  let f : K.X (-1) ⟶ (G.tensorPower (2 + q)).sheaf := K.d (-1) 0 ≫ e.hom
  have hd : Function.Surjective ((K.d (-1) 0).app ⊤) :=
    SquareKoszulSectionSurjectivity.lineBundleSquareKoszul_last_sections_surjective G hG ss hcover b hb
  have hf : Function.Surjective (f.app ⊤) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).surjective.comp hd
  intro t
  obtain ⟨n, v, a, ht⟩ := (KoszulPreviousPowerCopies.lineBundleSquareKoszul_previousTerm_finiteRetractCopies G ss b).sections_factor f (Finite.RetractSectionFactorization.section_postcomp_surjective_of_global_surjective f hf) t
  choose s hs using fun i => LineBundle.MapSectionFactorization.tensorPowerMap_exists_multiplying_section G 2 q (a i)
  refine ⟨n, s, v, ht.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  exact (congrArg (fun a => v i ≫ a) (hs i).symm).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ (G.tensorPowerAddIso 2 q).inv)
        (Section.MultiplicationProduct.section_comp_moduleSectionMultiply (G.tensorPower 2) (G.tensorPower q).sheaf
          (s i) (v i))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SquareSectionMultiplicationSurjectivity
