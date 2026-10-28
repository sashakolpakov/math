import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf
import OAI.AlgebraicTopology.Cohomology.Singular.IncreasingCochains

/-! # Manifold Smooth Open Reflection -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothOpenReflection

noncomputable section

/-! Smoothness of an actual manifold-valued simplex is reflected by an open
target inclusion. The neighborhood extension is restricted to the preimage
of the open target before it is made target-valued. -/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open scoped Simplicial ContDiff _root_.Manifold

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- For an open target, ambient smoothness is equivalent to smoothness as an
actual target-valued simplex with the inherited manifold structure. -/
theorem isManifoldSmoothSimplex_subtypeVal_iff (U : Opens M) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) :
    ManifoldSmooth.IsManifoldSmoothSimplex E
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp σ) ↔
      ManifoldSmooth.IsManifoldSmoothSimplex E σ := by
  classical
  constructor
  · rintro ⟨F, V, hV, hsub, hF, heq⟩
    let W := V ∩ F ⁻¹' (U : Set M)
    have hW : IsOpen W := hF.continuousOn.isOpen_inter_preimage hV U.isOpen
    have hWsub : Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        (x : Fin (n + 1) → ℝ)) ⊆ W := by
      rintro _ ⟨x, rfl⟩
      refine ⟨hsub ⟨x, rfl⟩, ?_⟩
      change F x ∈ U
      have hvalue := heq x
      change F x = (σ x : M) at hvalue
      rw [hvalue]
      exact (σ x).property
    let defaultPoint : U := σ (Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n + 1)))
    let G : (Fin (n + 1) → ℝ) → U :=
      fun x => if hx : x ∈ W then ⟨F x, hx.2⟩ else defaultPoint
    have hG : ∀ x ∈ W, (G x).val = F x := by
      intro x hx
      simp only [G, dite_eq_left hx]
    have hGval : ContMDiffOn 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, E) ∞
        (Subtype.val ∘ G) W :=
      (hF.mono Set.inter_subset_left).congr hG
    refine ⟨G, W, hW, hWsub, ?_, ?_⟩
    · intro x hx
      exact (ContMDiffWithinAt.subtypeVal_comp_iff U G W x).mp (hGval x hx)
    · intro x
      apply Subtype.ext
      exact (hG x (hWsub ⟨x, rfl⟩)).trans (heq x)
  · intro hσ
    exact ManifoldSmooth.IsManifoldSmoothSimplex.postcomp hσ
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U))

/-- The actual smooth singular subcomplex of an open manifold is exactly the
preimage of the ambient smooth singular subcomplex. -/
theorem manifoldSmoothSingularSubcomplex_open_preimage (U : Opens M) :
    ManifoldSmooth.manifoldSmoothSingularSubcomplex E U =
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).preimage
        (TopCat.toSSet.map (Opens.inclusion' (X := TopCat.of M) U)) := by
  ext n σ
  exact (isManifoldSmoothSimplex_subtypeVal_iff E U
    ((TopCat.of U).toSSetObjEquiv n σ)).symm

/-- The actual smooth singular simplices in one degree. -/
abbrev manifoldSmoothSimplices (M : Type) [TopologicalSpace M] [ChartedSpace E M] (n : ℕ) :=
  (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌

/-- The canonical smooth simplicial map from an open subset to its ambient manifold. -/
def manifoldSmoothOpenInclusion (U : Opens M) :
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet ⟶
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet :=
  ManifoldSmoothFunctor.manifoldSmoothSingularMap E E Subtype.val
    (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U))

@[simp]
theorem manifoldSmoothOpenInclusion_app_val (U : Opens M) (n : ℕ)
    (σ : manifoldSmoothSimplices E U n) :
    ((manifoldSmoothOpenInclusion E U).app (op ⦋n⦌) σ).val =
      (TopCat.toSSet.map (Opens.inclusion' (X := TopCat.of M) U)).app (op ⦋n⦌)
        σ.val := rfl

/-- An open inclusion is injective on the actual smooth simplices. -/
theorem manifoldSmoothOpenInclusion_injective (U : Opens M) (n : ℕ) :
    Function.Injective ((manifoldSmoothOpenInclusion E U).app (op ⦋n⦌)) := by
  intro σ τ h
  apply Subtype.ext
  apply IncreasingCochains.singularOpenInclusion_injective (X := TopCat.of M) U n
  exact congrArg Subtype.val h

/-- The ordinary codomain-restricted simplex is genuinely smooth in its open target. -/
def manifoldSmoothSimplexLift (U : Opens M) {n : ℕ}
    (σ : manifoldSmoothSimplices E M n)
    (hσ : Set.range (Coefficients.singularSimplicesEquivContinuousMap (TopCat.of M) n σ.val) ⊆ U) :
    manifoldSmoothSimplices E U n :=
  ⟨Topology.Euclidean.IncreasingCover.Globalization.singularSimplexLift (X := TopCat.of M) U σ.val hσ, by
    apply (isManifoldSmoothSimplex_subtypeVal_iff E U _).mp
    have hmap :
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp
          ((TopCat.of U).toSSetObjEquiv (op ⦋n⦌)
            (Topology.Euclidean.IncreasingCover.Globalization.singularSimplexLift
              (X := TopCat.of M) U σ.val hσ)) =
          (TopCat.of M).toSSetObjEquiv (op ⦋n⦌) σ.val := by
      ext x
      exact Topology.Euclidean.IncreasingCover.Globalization.singularSimplexLift_apply
        (X := TopCat.of M) U σ.val hσ x
    rw [hmap]
    exact σ.property⟩

@[simp]
theorem manifoldSmoothSimplexLift_spec (U : Opens M) {n : ℕ}
    (σ : manifoldSmoothSimplices E M n)
    (hσ : Set.range (Coefficients.singularSimplicesEquivContinuousMap (TopCat.of M) n σ.val) ⊆ U) :
    (manifoldSmoothOpenInclusion E U).app (op ⦋n⦌)
      (manifoldSmoothSimplexLift E U σ hσ) = σ := by
  apply Subtype.ext
  change (TopCat.toSSet.map (Opens.inclusion' (X := TopCat.of M) U)).app (op ⦋n⦌)
    (Topology.Euclidean.IncreasingCover.Globalization.singularSimplexLift (X := TopCat.of M) U σ.val hσ) = σ.val
  exact Topology.Euclidean.IncreasingCover.Globalization.map_singularSimplexLift (X := TopCat.of M) U σ.val hσ

/-- Every genuine manifold-smooth simplex is a genuine smooth simplex in some
member of an increasing open cover. -/
theorem exists_manifoldSmoothSimplex_lift (U : ℕ → Opens M) (hmono : Monotone U)
    (hcover : (⨆ i, U i) = ⊤) {n : ℕ} (σ : manifoldSmoothSimplices E M n) :
    ∃ i, ∃ τ : manifoldSmoothSimplices E (U i) n,
      (manifoldSmoothOpenInclusion E (U i)).app (op ⦋n⦌) τ = σ := by
  obtain ⟨i, hi⟩ := Topology.Euclidean.IncreasingCover.Globalization.exists_compact_subset_increasing_openCover
    U hmono hcover (Topology.Euclidean.IncreasingCover.Globalization.isCompact_singularSimplex_range σ.val)
  exact ⟨i, manifoldSmoothSimplexLift E (U i) σ hi, manifoldSmoothSimplexLift_spec E (U i) σ hi⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothOpenReflection
