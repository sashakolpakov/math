import OAI.AlgebraicTopology.FundamentalClass.IntegrationDuffyOrientation
import OAI.AlgebraicTopology.FundamentalClass.LocalSimplex
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.TopBidegree
import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import Mathlib.Analysis.Convex.Basic

/-! # Simplex Geometry -/

namespace OAI.AlgebraicTopology.FundamentalClass.SimplexGeometry.IntegrationConstruction

noncomputable section

section

/-! The positively ordered local simplex integrates a top form by the ordinary
Lebesgue integral on its geometric interior. -/

open _root_.CategoryTheory Opposite Set _root_.MeasureTheory
open OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration OAI.AlgebraicTopology.FundamentalClass.LocalSimplex.IntegrationGeometry
open scoped Simplicial _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

def simplexBarycenter (d : ℕ) : Fin d → ℝ := fun _ => ((d + 1 : ℕ) : ℝ)⁻¹

def positiveParameterization (d : ℕ) (t : Fin d → ℝ) : Fin d → ℝ :=
  IntegrationDuffyOrientation.Construction.Duffy.tail d t - simplexBarycenter d

theorem positiveParameterization_contDiff (d : ℕ) :
    ContDiff ℝ ∞ (positiveParameterization d) :=
  (contDiff_pi.mpr fun i : Fin d =>
    contDiff_pi.mp (DeRham.Comparison.DuffyCoordinates.Duffy.contDiff_coordinates d ∞) i.succ).sub contDiff_const

def positiveCube (d : ℕ) : DeRham.Comparison.ManifoldCubeIntegration.SmoothManifoldCube (Fin d → ℝ) (Fin d → ℝ) d :=
  ⟨positiveParameterization d, (positiveParameterization_contDiff d).contMDiff⟩

def positiveSmoothSimplex (d : ℕ) :
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex (Fin d → ℝ) (Fin d → ℝ)).toSSet _⦋d⦌ := by
  refine ⟨LocalSimplex.IntegrationGeometry.positiveSingularSimplex d, ?_⟩
  change Cohomology.Singular.ManifoldSmooth.IsManifoldSmoothSimplex (Fin d → ℝ) (LocalSimplex.IntegrationGeometry.positiveSimplex d)
  refine ⟨fun x i => x i.succ - ((d + 1 : ℕ) : ℝ)⁻¹, univ,
    isOpen_univ, subset_univ _, ?_, fun _ => rfl⟩
  exact (contDiff_pi.mpr fun i : Fin d =>
    (contDiff_apply ℝ ℝ i.succ).sub contDiff_const).contMDiff.contMDiffOn

theorem positiveCube_agrees (d : ℕ) (t : DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d) :
    positiveCube d t.val =
      (TopCat.of (Fin d → ℝ)).toSSetObjEquiv _ (positiveSmoothSimplex d).val
        (DeRham.Comparison.DuffyCoordinates.Duffy.toSimplex d t) := rfl

theorem positiveParameterization_fderiv (d : ℕ) (t : Fin d → ℝ) :
    fderiv ℝ (positiveParameterization d) t = fderiv ℝ (IntegrationDuffyOrientation.Construction.Duffy.tail d) t :=
  ((IntegrationDuffyOrientation.Construction.Duffy.tail_hasFDerivAt d t).sub_const (simplexBarycenter d)).fderiv.trans
    (IntegrationDuffyOrientation.Construction.Duffy.tail_hasFDerivAt d t).fderiv.symm

theorem positiveCube_pullback_top (d : ℕ)
    (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) (Fin d → ℝ) d) (t : Fin d → ℝ) :
    DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePullback (positiveCube d) form t (fun j => Pi.single j 1) =
      (fderiv ℝ (IntegrationDuffyOrientation.Construction.Duffy.tail d) t).toLinearMap.det •
        form.toNormedSpace (positiveParameterization d t) (Pi.basisFun ℝ (Fin d)) := by
  rw [DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePullback_apply]
  change (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (positiveParameterization d)
    (positiveParameterization_contDiff d).contMDiff form).toNormedSpace t _ = _
  rw [DeRham.Comparison.NormedManifoldPullback.toNormedSpace_pullback_self _ (positiveParameterization_contDiff d),
    OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback_apply_vectors,
    positiveParameterization_fderiv]
  simpa only [ContinuousAlternatingMap.coe_toAlternatingMap, Function.comp_def,
    Pi.basisFun_apply, ContinuousLinearMap.coe_coe] using
    DeRham.Comparison.TopBidegree.topAlternating_comp_apply (Pi.basisFun ℝ (Fin d))
    (form.toNormedSpace (positiveParameterization d t)).toAlternatingMap
    (fderiv ℝ (IntegrationDuffyOrientation.Construction.Duffy.tail d) t).toLinearMap (Pi.basisFun ℝ (Fin d))

theorem positiveSmoothSimplex_integral (d : ℕ)
    (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) (Fin d → ℝ) d) :
    DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration (positiveSmoothSimplex d) form =
      ∫ x in DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d,
        form.toNormedSpace (x - simplexBarycenter d) (Pi.basisFun ℝ (Fin d)) := by
  rw [DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_eq_cube _ (positiveCube d) (positiveCube_agrees d),
    DeRham.Comparison.ManifoldCubeIntegration.manifoldCubeIntegration_eq_integral]
  simp_rw [positiveCube_pullback_top]
  exact IntegrationDuffyOrientation.Construction.Duffy.signed_integral_simplex d
    (fun x => form.toNormedSpace (x - simplexBarycenter d) (Pi.basisFun ℝ (Fin d)))

end

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex
open Set _root_.MeasureTheory
open OAI.AlgebraicTopology.FundamentalClass.LocalSimplex.IntegrationGeometry OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration

set_option backward.isDefEq.respectTransparency false

theorem simplexInterior_isOpen (d : ℕ) : IsOpen (DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d) := by
  change IsOpen ({x : Fin d → ℝ | ∀ i, 0 < x i} ∩ {x | ∑ i, x i < 1})
  apply IsOpen.inter
  · simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  · exact isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

theorem simplexInterior_convex (d : ℕ) : Convex ℝ (DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d) := by
  change Convex ℝ ({x : Fin d → ℝ | ∀ i, 0 < x i} ∩ {x | ∑ i, x i < 1})
  apply Convex.inter
  · simp only [ofPred_forall]
    exact convex_iInter fun i => convex_halfSpace_gt
      (LinearMap.proj i : (Fin d → ℝ) →ₗ[ℝ] ℝ).isLinear 0
  · exact convex_halfSpace_lt
      { map_add := by intros; simp [Finset.sum_add_distrib]
        map_smul := by intros; simp [Finset.mul_sum] } 1

def positiveInterior (d : ℕ) : Set (Fin d → ℝ) :=
  (fun x => x + simplexBarycenter d) ⁻¹' DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d

theorem positiveInterior_isOpen (d : ℕ) : IsOpen (positiveInterior d) :=
  (simplexInterior_isOpen d).preimage (continuous_id.add continuous_const)

theorem positiveInterior_convex (d : ℕ) : Convex ℝ (positiveInterior d) :=
  (simplexInterior_convex d).translate_preimage_left (simplexBarycenter d)

theorem zero_mem_positiveInterior (d : ℕ) : (0 : Fin d → ℝ) ∈ positiveInterior d := by
  have hd : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
  change (0 + simplexBarycenter d) ∈ DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d
  rw [zero_add]
  constructor
  · intro i
    exact inv_pos.mpr hd
  · change ∑ _ : Fin d, ((d + 1 : ℕ) : ℝ)⁻¹ < 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← div_eq_mul_inv]
    exact (div_lt_one hd).mpr (by norm_cast; omega)

theorem positiveSimplex_mem_interior_iff (d : ℕ)
    (t : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    LocalSimplex.IntegrationGeometry.positiveSimplex d t ∈ positiveInterior d ↔ ∀ i, 0 < t.weights i := by
  have he : LocalSimplex.IntegrationGeometry.positiveSimplex d t + simplexBarycenter d = Fin.tail (t.weights : Fin (d + 1) → ℝ) := by
    ext i
    exact sub_add_cancel _ _
  change LocalSimplex.IntegrationGeometry.positiveSimplex d t + simplexBarycenter d ∈ DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d ↔ _
  rw [he]
  have hs := t.total_of_fintype
  rw [Fin.sum_univ_succ] at hs
  constructor
  · rintro ⟨hp, hsum⟩ i
    refine Fin.cases ?_ (fun j => hp j) i
    change ∑ i : Fin d, t.weights i.succ < 1 at hsum
    linarith
  · intro hp
    refine ⟨fun i => hp i.succ, ?_⟩
    change ∑ i : Fin d, t.weights i.succ < 1
    linarith [hp 0]

theorem positiveSimplex_face_outside (d : ℕ) (i : Fin (d + 2))
    (t : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    LocalSimplex.IntegrationGeometry.positiveSimplex (d + 1) (Convexity.StdSimplex.map i.succAbove t) ∉ positiveInterior (d + 1) := by
  rw [positiveSimplex_mem_interior_iff]
  intro h
  have hi := h i
  rw [DeRham.Comparison.DuffyFaces.Duffy.simplexFace_eq_insertNth, Fin.insertNth_apply_same] at hi
  exact lt_irrefl 0 hi

theorem positiveInterior_eq_image (d : ℕ) :
    positiveInterior d = (fun x => x - simplexBarycenter d) '' DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d := by
  ext x
  constructor
  · intro hx
    exact ⟨x + simplexBarycenter d, hx, add_sub_cancel_right _ _⟩
  · rintro ⟨y, hy, rfl⟩
    change y - simplexBarycenter d + simplexBarycenter d ∈ DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d
    simpa only [sub_add_cancel] using hy

theorem positiveSmoothSimplex_integral_interior (d : ℕ)
    (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) (Fin d → ℝ) d) :
    DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration (positiveSmoothSimplex d) form =
      ∫ x in positiveInterior d, form.toNormedSpace x (Pi.basisFun ℝ (Fin d)) := by
  rw [positiveSmoothSimplex_integral, positiveInterior_eq_image]
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    (simplexInterior_isOpen d).measurableSet
    (fun x _ => ((hasFDerivAt_id x).sub_const (simplexBarycenter d)).hasFDerivWithinAt)
    (fun x _ y _ h => sub_left_injective h)
    (fun x => form.toNormedSpace x (Pi.basisFun ℝ (Fin d)))
  have hd : (ContinuousLinearMap.id ℝ (Fin d → ℝ)).det = 1 := by
    change (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)).det = 1
    exact LinearMap.det_id
  simpa only [hd, abs_one, one_smul, id_eq] using h.symm

end

end OAI.AlgebraicTopology.FundamentalClass.SimplexGeometry.IntegrationConstruction
