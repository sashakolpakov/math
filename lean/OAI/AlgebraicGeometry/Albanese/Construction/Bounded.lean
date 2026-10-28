import OAI.AlgebraicGeometry.Albanese.Construction.CommonRefinement
import OAI.AlgebraicGeometry.Albanese.Construction.MaximalRefinement
import OAI.AlgebraicGeometry.Albanese.Construction.Trivial

/-! # Bounded -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.Bounded

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

/-- A uniform numerical bound on generated targets gives a target of
maximal dimension. This lemma isolates the numerical step of the construction. -/
theorem exists_maximal_dimension_target (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (N : ℕ)
    (hN : ∀ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
      x₀ ≫ a = 1 → GeneratedClosed.Generates X A a → Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap ≤ N) :
    ∃ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : X.toOver ⟶ B.toOver),
      x₀ ≫ b = 1 ∧ GeneratedClosed.Generates X B b ∧
      ∀ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
        x₀ ≫ a = 1 → GeneratedClosed.Generates X A a →
        Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap ≤
          Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap := by
  classical
  let P (n : ℕ) := ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
    x₀ ≫ a = 1 ∧ GeneratedClosed.Generates X A a ∧ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap = n
  obtain ⟨A₀, a₀, ha₀, hg₀⟩ := Trivial.exists_pointed_generating_target X x₀
  obtain ⟨B, b, hb, hgen, hdim⟩ :=
    Nat.findGreatest_spec (P := P) (hN A₀ a₀ ha₀ hg₀) ⟨A₀, a₀, ha₀, hg₀, rfl⟩
  refine ⟨B, b, hb, hgen, fun A a ha hg => ?_⟩
  rw [hdim]
  exact Nat.le_findGreatest (hN A a ha hg) ⟨A, a, ha, hg, rfl⟩

/-- A generated target of maximal dimension, with no further refinement
in that dimension, has the required Albanese universal property. -/
theorem universal_of_maximal_target (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : X.toOver ⟶ B.toOver)
    (hb : x₀ ≫ b = 1) (hgen : GeneratedClosed.Generates X B b)
    (hmax : ∀ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
      x₀ ≫ a = 1 → GeneratedClosed.Generates X A a →
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap ≤
        Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap)
    (hstable : ∀ r : MaximalRefinement.GeneratingRefinement X x₀ B b, IsIso r.projection) :
    ∀ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver), x₀ ≫ f = 1 →
      ∃! φ : B.toOver ⟶ A.toOver, IsMonHom φ ∧ b ≫ φ = f := by
  intro A f hf
  obtain ⟨C, c, p, q, hc, hcg, hp, hq, hcp, hcq⟩ :=
    CommonRefinement.exists_common_generated_target X x₀ B A b f hb hf
  let _ := hp
  let _ := hq
  have hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension C.variety.structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap :=
    le_antisymm (hmax C c hc hcg) (DominantDimension.refinement_dimension_le X C B c b p hcp hgen)
  let r : MaximalRefinement.GeneratingRefinement X x₀ B b := ⟨C, c, p, hc, hp, hcp, hcg, hd⟩
  have : IsIso p := hstable r
  let φ : B.toOver ⟶ A.toOver := (asIso p).inv ≫ q
  have hφ : IsMonHom φ := inferInstanceAs (IsMonHom ((asIso p).inv ≫ q))
  have hbφ : b ≫ φ = f := by
    rw [← hcp]
    change (c ≫ (asIso p).hom) ≫ (asIso p).inv ≫ q = f
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hcq
  refine ⟨φ, ⟨hφ, hbφ⟩, ?_⟩
  rintro ψ ⟨hψ, hbψ⟩
  let _ := hψ
  exact GeneratingWords.generating_hom_ext X B A b hgen ψ φ (hbψ.trans hbφ.symm)

/-- The algebraic construction of the universal target from a dimension
bound. The bound itself remains a separate geometric theorem. -/
theorem exists_albanese_of_dimension_bound (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (N : ℕ)
    (hN : ∀ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
      x₀ ≫ a = 1 → GeneratedClosed.Generates X A a → Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap ≤ N) :
    ∃ (Alb : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ Alb.toOver), x₀ ≫ a = 1 ∧
      ∀ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver), x₀ ≫ f = 1 →
        ∃! φ : Alb.toOver ⟶ A.toOver, IsMonHom φ ∧ a ≫ φ = f := by
  obtain ⟨B, b, hb, hgen, hmax⟩ := exists_maximal_dimension_target X x₀ N hN
  obtain ⟨r, hr⟩ := MaximalRefinement.exists_refinement_without_further_refinements X x₀ B b hb hgen
  refine ⟨r.target, r.map, r.pointed, ?_⟩
  apply universal_of_maximal_target X x₀ r.target r.map r.pointed r.generates _ hr
  intro A a ha hg
  rw [r.dimension]
  exact hmax A a ha hg

end

end OAI.AlgebraicGeometry.Albanese.Construction.Bounded
