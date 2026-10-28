import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.TermTensorInclusion

/-! # Homogeneous Projection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.HomogeneousProjection.ProjectiveCech

noncomputable section

/-! Projection to an actual homogeneous degree commutes with the projective Čech differential. -/

open _root_.MvPolynomial DirectSum

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

theorem moduleChartDegreeProjection_restriction {s t : Finset σ} (h : s ⊆ t)
    (d : ℤ) (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (TermTensorInclusion.ProjectiveCech.moduleChartDegreeProjection R M ℳ s d x).val =
      (TermTensorInclusion.ProjectiveCech.moduleChartDegreeProjection R M ℳ t d (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h x)).val := by
  let := Localized.Grading.GradedModules.localizedDegreeDecomposition (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s)
  let := Localized.Grading.GradedModules.localizedDegreeDecomposition (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ
    (LaurentMonomials.ProjectiveCech.inversionMonomial R t) (t.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R t)
  exact Graded.ModuleGenerators.GradedModules.map_homogeneous_component
    (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ))
    (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (LaurentMonomials.ProjectiveCech.inversionMonomial R t) (t.card : ℤ))
    (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h).toAddMonoidHom
    (fun d x hx => Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction_degree R M ℳ h d x hx) d x

def moduleCechHomogeneousProjection (d : ℤ) :
    ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M →ₗ[R] ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M :=
  LinearMap.pi (fun s => ((Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d).subtype.comp
    (TermTensorInclusion.ProjectiveCech.moduleChartDegreeProjection R M ℳ s d)).comp (LinearMap.proj s))

omit [LinearOrder σ] in
theorem moduleCechHomogeneousProjection_mem (d : ℤ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d (moduleCechHomogeneousProjection R M ℳ d f) :=
  fun s => (TermTensorInclusion.ProjectiveCech.moduleChartDegreeProjection R M ℳ s d (f s)).property

omit [LinearOrder σ] in
theorem moduleCechHomogeneousProjection_card (d : ℤ) (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f) :
    ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q (moduleCechHomogeneousProjection R M ℳ d f) := by
  intro s hs
  change (TermTensorInclusion.ProjectiveCech.moduleChartDegreeProjection R M ℳ s d (f s)).val = 0
  rw [hf s hs, map_zero]
  rfl

omit [LinearOrder σ] in
theorem moduleCechHomogeneousProjection_of_homogeneous (d : ℤ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f) : moduleCechHomogeneousProjection R M ℳ d f = f := by
  funext s
  exact congrArg Subtype.val (TermTensorInclusion.ProjectiveCech.moduleChartDegreeProjection_subtype R M ℳ s d ⟨f s, hf s⟩)

theorem moduleCechHomogeneousProjection_differential (d : ℤ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M (moduleCechHomogeneousProjection R M ℳ d f) =
      moduleCechHomogeneousProjection R M ℳ d (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f) := by
  funext s
  change (∑ i ∈ s, Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i s)
    (TermTensorInclusion.ProjectiveCech.moduleChartDegreeProjection R M ℳ (s.erase i) d (f (s.erase i))).val) =
    (TermTensorInclusion.ProjectiveCech.moduleChartDegreeProjection R M ℳ s d
      (∑ i ∈ s, Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i s) (f (s.erase i)))).val
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Finset.sum_congr rfl
  intro i _
  rw [moduleChartDegreeProjection_restriction]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.HomogeneousProjection.ProjectiveCech
