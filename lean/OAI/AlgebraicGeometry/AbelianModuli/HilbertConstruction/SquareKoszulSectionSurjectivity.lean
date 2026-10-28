import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.PowerKoszulAcyclicity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.AcyclicModuleSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulAcyclic

/-! # Square Koszul Section Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SquareKoszulSectionSurjectivity

noncomputable section

/-! A covering family of sections of a square gives surjectivity at the
last global-section map of each Koszul complex with positive-power coefficients. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem lineBundleSquareKoszul_last_sections_surjective
    {X : Scheme.{u}} (G : Line.Bundles.LineBundle X)
    (hG : ∀ b : ℕ, 0 < b → ∀ q : ℕ, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (G.tensorPower b).sheaf (q + 1)))
    (ss : List (Line.Bundles.structureModule X ⟶ (G.tensorPower 2).sheaf))
    (hcover : ∀ x : X, ∃ s ∈ ss, x ∈ Ample.LineBundles.sectionNonvanishing s)
    (b : ℕ) (hb : 0 < b) :
    Function.Surjective
      (((LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex (G.tensorPower 2) (G.tensorPower b).sheaf ss).d (-1) 0).app ⊤) := by
  let L := G.tensorPower 2
  let M := (G.tensorPower b).sheaf
  let K := LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss
  let I := {s : Line.Bundles.structureModule X ⟶ L.sheaf // s ∈ ss}
  have hK : K.Acyclic := by
    apply LineBundle.SectionKoszulAcyclic.lineBundleSectionKoszulComplex_acyclic L M ss (fun s : I => Ample.LineBundles.sectionNonvanishing s.val)
    · intro x
      obtain ⟨s, hs, hx⟩ := hcover x
      exact ⟨⟨s, hs⟩, hx⟩
    · intro s
      exact ⟨s.val, s.property,
        (Section.Nonvanishing.isIso_pullbackSection_iff (Ample.LineBundles.sectionNonvanishing s.val).ι s.val).mp inferInstance⟩
  exact Bounded.AcyclicModuleSections.bounded_acyclic_moduleComplex_last_sections_surjective K hK
    (fun i q => Positive.PowerKoszulAcyclicity.lineBundleSquareKoszul_terms_acyclic G hG ss b hb i q) ss.length
    (fun i hi => LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex_isZero_X L M ss i (Or.inl hi))
    (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex_isZero_X L M ss 1 (Or.inr (by decide)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SquareKoszulSectionSurjectivity
