import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth
import OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen

/-! # Manifold Smooth Models -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothModels

noncomputable section

/-!
# Compatibility of manifold smooth simplices with the normed-space models

For the standard chart on a real normed space, manifold smoothness is ordinary
smoothness. For an open subset with its inherited charts, the same definition
agrees with the previously constructed subset-valued smooth singular complex.
The open-target argument constructs a genuine target-valued neighborhood
extension; it does not assume that an ambient extension stays in the open set.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff _root_.Manifold

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The standard manifold structure on a normed space gives the old smooth
neighborhood-extension condition. -/
theorem isManifoldSmoothSimplex_self_iff {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)) :
    ManifoldSmooth.IsManifoldSmoothSimplex E σ ↔ Smooth.IsSmoothSimplex σ := by
  simp only [ManifoldSmooth.IsManifoldSmoothSimplex, Smooth.IsSmoothSimplex, contMDiffOn_iff_contDiffOn]

/-- The two genuine smooth singular subcomplexes of a normed space agree. -/
theorem manifoldSmoothSingularSubcomplex_self :
    ManifoldSmooth.manifoldSmoothSingularSubcomplex E E = Smooth.smoothSingularSubcomplex E := by
  ext n σ
  exact isManifoldSmoothSimplex_self_iff E _

/-- On an open subset with its inherited charts, manifold-smooth simplices are
exactly the subset-valued smooth simplices previously defined in the ambient space. -/
theorem isManifoldSmoothSimplex_open_iff (U : TopologicalSpace.Opens E) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) :
    ManifoldSmooth.IsManifoldSmoothSimplex E σ ↔ SmoothOpen.IsSmoothSimplexIn (U : Set E) σ := by
  classical
  constructor
  · rintro ⟨F, V, hV, hsub, hF, heq⟩
    refine ⟨Subtype.val ∘ F, V, hV, hsub, ?_, ?_⟩
    · apply contMDiffOn_iff_contDiffOn.mp
      intro x hx
      exact (ContMDiffWithinAt.subtypeVal_comp_iff U F V x).mpr (hF x hx)
    · intro x
      exact congrArg Subtype.val (heq x)
  · intro hσ
    obtain ⟨F, V, hV, hsub, hF, hmap, heq⟩ :=
      (SmoothOpen.isSmoothSimplexIn_iff_extension U.isOpen σ).mp hσ
    let d : U := σ (Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n + 1)))
    let G : (Fin (n + 1) → ℝ) → U :=
      fun x => if hx : x ∈ V then ⟨F x, hmap hx⟩ else d
    have hG : ∀ x ∈ V, (G x).val = F x := by
      intro x hx
      simp only [G, dite_eq_left hx]
    have hGval : ContDiffOn ℝ ∞ (Subtype.val ∘ G) V := hF.congr hG
    refine ⟨G, V, hV, hsub, ?_, ?_⟩
    · intro x hx
      exact (ContMDiffWithinAt.subtypeVal_comp_iff U G V x).mp
        (hGval.contMDiffOn x hx)
    · intro x
      apply Subtype.ext
      exact (hG x (hsub ⟨x, rfl⟩)).trans (heq x)

/-- The open-subset manifold model is the old subset smooth singular subcomplex. -/
theorem manifoldSmoothSingularSubcomplex_open (U : TopologicalSpace.Opens E) :
    ManifoldSmooth.manifoldSmoothSingularSubcomplex E U = SmoothOpen.subsetSmoothSingularSubcomplex (U : Set E) := by
  ext n σ
  change ManifoldSmooth.IsManifoldSmoothSimplex E ((TopCat.of U).toSSetObjEquiv n σ) ↔
    SmoothOpen.IsSmoothSimplexIn (U : Set E) ((TopCat.of U).toSSetObjEquiv n σ)
  exact isManifoldSmoothSimplex_open_iff E U _

/-- The canonical simplicial identification for the standard normed-space model. -/
def manifoldSmoothSelfIso :
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E E).toSSet ≅ (Smooth.smoothSingularSubcomplex E).toSSet :=
  SSet.Subcomplex.eqToIso (manifoldSmoothSingularSubcomplex_self E)

/-- The canonical simplicial identification for an open subset with inherited charts. -/
def manifoldSmoothOpenIso (U : TopologicalSpace.Opens E) :
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet ≅
      (SmoothOpen.subsetSmoothSingularSubcomplex (U : Set E)).toSSet :=
  SSet.Subcomplex.eqToIso (manifoldSmoothSingularSubcomplex_open E U)

@[reassoc (attr := simp)]
theorem manifoldSmoothSelfIso_inv_inclusion :
    (manifoldSmoothSelfIso E).inv ≫ ManifoldSmooth.manifoldSmoothInclusion E E =
      Smooth.smoothSingularInclusion E :=
  SSet.Subcomplex.homOfLE_ι (manifoldSmoothSingularSubcomplex_self E).symm.le

@[reassoc (attr := simp)]
theorem manifoldSmoothOpenIso_inv_inclusion (U : TopologicalSpace.Opens E) :
    (manifoldSmoothOpenIso E U).inv ≫ ManifoldSmooth.manifoldSmoothInclusion E U =
      (SmoothOpen.subsetSmoothSingularSubcomplex (U : Set E)).ι :=
  SSet.Subcomplex.homOfLE_ι (manifoldSmoothSingularSubcomplex_open E U).symm.le

variable {R : Type} [Ring R]

/-- The manifold-smooth cochains on a normed space are the existing smooth
singular cochains, with their actual differentials. -/
def manifoldSmoothSelfCochainsIso (A : ModuleCat.{0} R) :
    ManifoldSmooth.manifoldSmoothCochains E A E ≅ Smooth.smoothSingularCochains A E :=
  (Functor.simplicialCochainsFunctor A).mapIso (manifoldSmoothSelfIso E).symm.op

/-- The manifold-smooth cochains on an open subset are the existing subset-smooth
cochains, with their actual differentials. -/
def manifoldSmoothOpenCochainsIso (U : TopologicalSpace.Opens E) (A : ModuleCat.{0} R) :
    ManifoldSmooth.manifoldSmoothCochains E A U ≅ SmoothOpen.subsetSmoothCochains A (U : Set E) :=
  (Functor.simplicialCochainsFunctor A).mapIso (manifoldSmoothOpenIso E U).symm.op

@[reassoc (attr := simp)]
theorem manifoldSmoothSelfCochainRestriction_iso_hom (A : ModuleCat.{0} R) :
    ManifoldSmooth.manifoldSmoothCochainRestriction E A E ≫ (manifoldSmoothSelfCochainsIso E A).hom =
      Smooth.smoothSingularCochainRestriction A E := by
  change Functor.simplicialPullback A (ManifoldSmooth.manifoldSmoothInclusion E E) ≫
      Functor.simplicialPullback A (manifoldSmoothSelfIso E).inv =
    Functor.simplicialPullback A (Smooth.smoothSingularInclusion E)
  rw [← Functor.simplicialPullback_comp, manifoldSmoothSelfIso_inv_inclusion]

@[reassoc (attr := simp)]
theorem manifoldSmoothOpenCochainRestriction_iso_hom (U : TopologicalSpace.Opens E)
    (A : ModuleCat.{0} R) :
    ManifoldSmooth.manifoldSmoothCochainRestriction E A U ≫ (manifoldSmoothOpenCochainsIso E U A).hom =
      SmoothOpen.subsetSmoothCochainRestriction A (U : Set E) := by
  change Functor.simplicialPullback A (ManifoldSmooth.manifoldSmoothInclusion E U) ≫
      Functor.simplicialPullback A (manifoldSmoothOpenIso E U).inv =
    Functor.simplicialPullback A (SmoothOpen.subsetSmoothSingularSubcomplex (U : Set E)).ι
  rw [← Functor.simplicialPullback_comp, manifoldSmoothOpenIso_inv_inclusion]

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothModels
