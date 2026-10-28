import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveZeroLocus
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Immersion

/-! # Segre At -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre

noncomputable section

/-!
# A projective embedding of a product of projective spaces

The Segre map sends a pair of homogeneous coordinate vectors to their pairwise
products. This supplies a single projective ambient space for a graph lying
in a product of projective embeddings.
-/

open Set
open scoped _root_.Topology

variable {ι κ : Type*}

def outer (v : ι → ℂ) (w : κ → ℂ) : ι × κ → ℂ := fun ij => v ij.1 * w ij.2

theorem outer_ne_zero {v : ι → ℂ} {w : κ → ℂ} (hv : v ≠ 0) (hw : w ≠ 0) :
    outer v w ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  intro h
  exact (mul_ne_zero hi hj) (congrFun h (i, j))

/-- The Segre map on actual projectivization quotients. -/
def segre (p : Projectivization ℂ (ι → ℂ)) (q : Projectivization ℂ (κ → ℂ)) :
    Projectivization ℂ (ι × κ → ℂ) :=
  Projectivization.mk ℂ (outer p.rep q.rep) (outer_ne_zero p.rep_nonzero q.rep_nonzero)

theorem segre_mk (v : ι → ℂ) (w : κ → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    segre (Projectivization.mk ℂ v hv) (Projectivization.mk ℂ w hw) =
      Projectivization.mk ℂ (outer v w) (outer_ne_zero hv hw) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ w hw
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(a : ℂ) * (b : ℂ), ?_⟩
  rw [← ha, ← hb]
  ext ij
  simp only [outer, Pi.smul_apply, Units.smul_def, smul_eq_mul]
  ring

/-- The Segre map determines both of its projective factors. -/
theorem segre_injective : Function.Injective
    (fun pq : Projectivization ℂ (ι → ℂ) × Projectivization ℂ (κ → ℂ) => segre pq.1 pq.2) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp p.rep_nonzero
  obtain ⟨j, hj⟩ := Function.ne_iff.mp q.rep_nonzero
  change p.rep i ≠ 0 at hi
  change q.rep j ≠ 0 at hj
  have hcoord (a : ι) (b : κ) : c * (p'.rep a * q'.rep b) = p.rep a * q.rep b :=
    congrFun hc (a, b)
  apply Prod.ext
  · rw [← p.mk_rep, ← p'.mk_rep]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨c * q'.rep j / q.rep j, ?_⟩
    ext a
    simp only [Pi.smul_apply, smul_eq_mul]
    have hh := hcoord a j
    field_simp [hj]
    linear_combination hh
  · rw [← q.mk_rep, ← q'.mk_rep]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨c * p'.rep i / p.rep i, ?_⟩
    ext b
    simp only [Pi.smul_apply, smul_eq_mul]
    have hh := hcoord i b
    field_simp [hi]
    linear_combination hh

/-- The pairwise-product coordinates are continuous on vectors. -/
theorem continuous_outer : Continuous (fun vw : (ι → ℂ) × (κ → ℂ) => outer vw.1 vw.2) := by
  apply continuous_pi
  intro ij
  exact ((continuous_apply ij.1).comp continuous_fst).mul
    ((continuous_apply ij.2).comp continuous_snd)

/-- The Segre map is continuous for the ordinary projective quotient topology. -/
theorem continuous_segre : Continuous
    (fun pq : Projectivization ℂ (ι → ℂ) × Projectivization ℂ (κ → ℂ) => segre pq.1 pq.2) := by
  let π₁ := Projectivization.mk' ℂ (V := ι → ℂ)
  let π₂ := Projectivization.mk' ℂ (V := κ → ℂ)
  have hπ₁ := ComplexPoints.Analytic.ProjectiveCompactness.isQuotientMap_projectivization_mk' ℂ (ι → ℂ)
  have hπ₂ := ComplexPoints.Analytic.ProjectiveCompactness.isQuotientMap_projectivization_mk' ℂ (κ → ℂ)
  have hπ : Topology.IsQuotientMap (Prod.map π₁ π₂) :=
    (ComplexPoints.Analytic.ProjectiveZeroLocus.isOpenMap_projectivization_mk'.prodMap
      ComplexPoints.Analytic.ProjectiveZeroLocus.isOpenMap_projectivization_mk').isQuotientMap
        (hπ₁.continuous.prodMap hπ₂.continuous) (hπ₁.surjective.prodMap hπ₂.surjective)
  apply hπ.continuous_iff.mpr
  have hout : Continuous (fun vw : {v : ι → ℂ // v ≠ 0} × {w : κ → ℂ // w ≠ 0} =>
      outer vw.1.val vw.2.val) :=
    continuous_outer.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  have h := (ComplexPoints.Analytic.ProjectiveCompactness.continuous_projectivization_mk' ℂ (ι × κ → ℂ)).comp
    (hout.subtype_mk (fun vw => outer_ne_zero vw.1.property vw.2.property))
  change Continuous (fun vw : {v : ι → ℂ // v ≠ 0} × {w : κ → ℂ // w ≠ 0} =>
    segre (Projectivization.mk ℂ vw.1.val vw.1.property)
      (Projectivization.mk ℂ vw.2.val vw.2.property))
  simpa only [Function.comp_def, Projectivization.mk'_eq_mk, segre_mk] using h

/-- In finite dimensions the Segre map is a closed embedding. -/
theorem isClosedEmbedding_segre [Fintype ι] [Fintype κ] :
    Topology.IsClosedEmbedding
      (fun pq : Projectivization ℂ (ι → ℂ) × Projectivization ℂ (κ → ℂ) => segre pq.1 pq.2) :=
  continuous_segre.isClosedEmbedding segre_injective

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

/-- The projective coordinate ratios of the Segre map are products of the
two factor ratios. -/
theorem ratio_segre (i a : ι) (j b : κ)
    (p : Projectivization ℂ (ι → ℂ)) (q : Projectivization ℂ (κ → ℂ)) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio (i, j) (a, b) (segre p q) = Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i a p * Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio j b q := by
  induction p using Projectivization.ind with
  | h v hv =>
      induction q using Projectivization.ind with
      | h w hw =>
          simp only [segre_mk, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio_mk, outer]
          exact (div_mul_div_comm _ _ _ _).symm

/-- A Segre coordinate patch is exactly the product of its factor patches. -/
theorem inPatch_segre_iff (i : ι) (j : κ)
    (p : Projectivization ℂ (ι → ℂ)) (q : Projectivization ℂ (κ → ℂ)) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (i, j) (segre p q) ↔ Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p ∧ Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j q := by
  induction p using Projectivization.ind with
  | h v hv =>
      induction q using Projectivization.ind with
      | h w hw => simp only [segre_mk, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff, outer, mul_ne_zero_iff]

/-- Insert the distinguished homogeneous coordinate with value one. -/
def fillCoordinate (i : ι) (z : {a : ι // a ≠ i} → ℂ) (a : ι) : ℂ := by
  classical
  exact if h : a = i then 1 else z ⟨a, h⟩

theorem ratio_projectiveChart_symm (i a : ι) (z : {a : ι // a ≠ i} → ℂ) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i a ((ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).symm z) = fillCoordinate i z a := by
  classical
  by_cases ha : a = i
  · subst a
    have hp := (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).map_target (mem_univ z)
    change Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i i ((ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).symm z) = 1 at hp
    simpa [fillCoordinate] using hp
  · have h := congrFun ((ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).right_inv (mem_univ z)) ⟨a, ha⟩
    simpa only [ComplexPoints.Analytic.ProjectiveCharts.projectiveChart_apply, fillCoordinate, dite_eq_right ha] using h

/-- The polynomial formula for Segre coordinates in standard affine patches. -/
def affineSegre (i : ι) (j : κ)
    (z : ({a : ι // a ≠ i} → ℂ) × ({b : κ // b ≠ j} → ℂ))
    (ab : {ab : ι × κ // ab ≠ (i, j)}) : ℂ :=
  fillCoordinate i z.1 ab.val.1 * fillCoordinate j z.2 ab.val.2

theorem projectiveChart_segre (i : ι) (j : κ)
    (z : ({a : ι // a ≠ i} → ℂ) × ({b : κ // b ≠ j} → ℂ)) :
    ComplexPoints.Analytic.ProjectiveCharts.projectiveChart (i, j)
      (segre ((ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).symm z.1)
        ((ComplexPoints.Analytic.ProjectiveCharts.projectiveChart j).symm z.2)) = affineSegre i j z := by
  ext ab
  change Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio (i, j) (ab.val.1, ab.val.2)
    (segre ((ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).symm z.1)
      ((ComplexPoints.Analytic.ProjectiveCharts.projectiveChart j).symm z.2)) =
    fillCoordinate i z.1 ab.val.1 * fillCoordinate j z.2 ab.val.2
  rw [ratio_segre, ratio_projectiveChart_symm, ratio_projectiveChart_symm]

variable [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

theorem differentiable_affineSegre (i : ι) (j : κ) : Differentiable ℂ (affineSegre i j) := by
  classical
  have hfst : Differentiable ℂ
      (Prod.fst : (({a : ι // a ≠ i} → ℂ) × ({b : κ // b ≠ j} → ℂ)) →
        ({a : ι // a ≠ i} → ℂ)) := differentiable_fst
  have hsnd : Differentiable ℂ
      (Prod.snd : (({a : ι // a ≠ i} → ℂ) × ({b : κ // b ≠ j} → ℂ)) →
        ({b : κ // b ≠ j} → ℂ)) := differentiable_snd
  apply differentiable_pi.mpr
  intro ab
  change Differentiable ℂ (fun z : ({a : ι // a ≠ i} → ℂ) × ({b : κ // b ≠ j} → ℂ) =>
    fillCoordinate i z.1 ab.val.1 * fillCoordinate j z.2 ab.val.2)
  apply Differentiable.fun_mul
  · by_cases ha : ab.val.1 = i
    · simp only [fillCoordinate, dite_eq_left ha]
      exact differentiable_const _
    · simp only [fillCoordinate, dite_eq_right ha]
      exact (differentiable_apply ⟨ab.val.1, ha⟩).comp hfst
  · by_cases hb : ab.val.2 = j
    · simp only [fillCoordinate, dite_eq_left hb]
      exact differentiable_const _
    · simp only [fillCoordinate, dite_eq_right hb]
      exact (differentiable_apply ⟨ab.val.2, hb⟩).comp hsnd

/-- The original affine coordinates occur as one row and one column of the
Segre coordinates, so coordinate recovery is linear and continuous. -/
def affineUnSegre (i : ι) (j : κ) :
    ({ab : ι × κ // ab ≠ (i, j)} → ℂ) →L[ℂ]
      (({a : ι // a ≠ i} → ℂ) × ({b : κ // b ≠ j} → ℂ)) where
  toFun z := (fun a => z ⟨(a.val, j), fun h => a.property (congrArg Prod.fst h)⟩,
    fun b => z ⟨(i, b.val), fun h => b.property (congrArg Prod.snd h)⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_pi (fun _ => continuous_apply _)).prodMk
    (continuous_pi (fun _ => continuous_apply _))

omit [Fintype ι] [Fintype κ] in
theorem affineUnSegre_leftInverse (i : ι) (j : κ) :
    Function.LeftInverse (affineUnSegre i j) (affineSegre i j) := by
  intro z
  apply Prod.ext
  · ext a
    simp [affineUnSegre, affineSegre, fillCoordinate, a.property]
  · ext b
    simp [affineUnSegre, affineSegre, fillCoordinate, b.property]

theorem isEmbedding_affineSegre (i : ι) (j : κ) : Topology.IsEmbedding (affineSegre i j) :=
  (affineUnSegre_leftInverse i j).isEmbedding (affineUnSegre i j).continuous
    (differentiable_affineSegre i j).continuous

theorem fderiv_affineSegre_injective (i : ι) (j : κ)
    (x : ({a : ι // a ≠ i} → ℂ) × ({b : κ // b ≠ j} → ℂ)) :
    Function.Injective (fderiv ℂ (affineSegre i j) x) := by
  have heq : (affineUnSegre i j) ∘ affineSegre i j = id :=
    (affineUnSegre_leftInverse i j).comp_eq_id
  have hd := congrArg (fun h => fderiv ℂ h x) heq
  rw [fderiv_comp x (affineUnSegre i j).differentiableAt
    ((differentiable_affineSegre i j) x), ContinuousLinearMap.fderiv, fderiv_id] at hd
  have hleft : Function.LeftInverse (affineUnSegre i j) (fderiv ℂ (affineSegre i j) x) := by
    intro z
    exact congrArg (fun L => L z) hd
  exact hleft.injective

/-- The Segre image in each affine patch has genuine local holomorphic equations. -/
theorem holomorphicZeroSetAt_affineSegre (i : ι) (j : κ)
    (x : ({a : ι // a ≠ i} → ℂ) × ({b : κ // b ≠ j} → ℂ)) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (range (affineSegre i j))
      (affineSegre i j x) := by
  have hemb : Topology.IsEmbedding
      (fun z : (univ : Set (({a : ι // a ≠ i} → ℂ) × ({b : κ // b ≠ j} → ℂ))) =>
        affineSegre i j z) := (isEmbedding_affineSegre i j).comp Topology.IsEmbedding.subtypeVal
  simpa only [image_univ] using Immersion.Constructions.Cone.holomorphicZeroSetAt_image_of_embedding
    isOpen_univ (differentiable_affineSegre i j).differentiableOn hemb (mem_univ x)
      (fderiv_affineSegre_injective i j x)

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts

/-- Reinsert the omitted-coordinate indexing used by the projective chart. -/
def expandFin {n : ℕ} (i : Fin (n + 1)) :
    (Fin n → ℂ) →L[ℂ] ({a : Fin (n + 1) // a ≠ i} → ℂ) :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj ((finSuccAboveEquiv i).symm a)

def contractFin {n : ℕ} (i : Fin (n + 1)) :
    ({a : Fin (n + 1) // a ≠ i} → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (finSuccAboveEquiv i a)

theorem contractFin_expandFin {n : ℕ} (i : Fin (n + 1)) :
    Function.LeftInverse (contractFin i) (expandFin i) := by
  intro z
  ext a
  simp [contractFin, expandFin]

theorem expandFin_projectiveFinChart {n : ℕ} (i : Fin (n + 1))
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) :
    expandFin i (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i p) = ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i p := by
  ext a
  obtain ⟨b, rfl⟩ := (finSuccAboveEquiv i).surjective a
  simp [expandFin, ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart_apply]
  rfl

/-- The affine Segre map with the factors indexed by standard `Fin` coordinates. -/
def finAffineSegre {n m : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1))
    (z : (Fin n → ℂ) × (Fin m → ℂ)) :
    ({ab : Fin (n + 1) × Fin (m + 1) // ab ≠ (i, j)} → ℂ) :=
  affineSegre i j (expandFin i z.1, expandFin j z.2)

def finAffineUnSegre {n m : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1)) :
    ({ab : Fin (n + 1) × Fin (m + 1) // ab ≠ (i, j)} → ℂ) →L[ℂ]
      ((Fin n → ℂ) × (Fin m → ℂ)) :=
  ((contractFin i).prodMap (contractFin j)).comp (affineUnSegre i j)

theorem finAffineUnSegre_leftInverse {n m : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1)) :
    Function.LeftInverse (finAffineUnSegre i j) (finAffineSegre i j) := by
  intro z
  change ((contractFin i).prodMap (contractFin j))
    (affineUnSegre i j (affineSegre i j (expandFin i z.1, expandFin j z.2))) = z
  rw [affineUnSegre_leftInverse]
  exact Prod.ext (contractFin_expandFin i z.1) (contractFin_expandFin j z.2)

theorem differentiable_finAffineSegre {n m : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1)) :
    Differentiable ℂ (finAffineSegre i j) :=
  (differentiable_affineSegre i j).comp
    ((expandFin i).prodMap (expandFin j)).differentiable

theorem isEmbedding_finAffineSegre {n m : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1)) :
    Topology.IsEmbedding (finAffineSegre i j) :=
  (finAffineUnSegre_leftInverse i j).isEmbedding (finAffineUnSegre i j).continuous
    (differentiable_finAffineSegre i j).continuous

theorem fderiv_finAffineSegre_injective {n m : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1))
    (x : (Fin n → ℂ) × (Fin m → ℂ)) :
    Function.Injective (fderiv ℂ (finAffineSegre i j) x) := by
  have heq : (finAffineUnSegre i j) ∘ finAffineSegre i j = id :=
    (finAffineUnSegre_leftInverse i j).comp_eq_id
  have hd := congrArg (fun h => fderiv ℂ h x) heq
  rw [fderiv_comp x (finAffineUnSegre i j).differentiableAt
    ((differentiable_finAffineSegre i j) x), ContinuousLinearMap.fderiv, fderiv_id] at hd
  have hleft : Function.LeftInverse (finAffineUnSegre i j) (fderiv ℂ (finAffineSegre i j) x) := by
    intro z
    exact congrArg (fun L => L z) hd
  exact hleft.injective

theorem projectiveChart_segre_fin {n m : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1))
    {p : Projectivization ℂ (Fin (n + 1) → ℂ)}
    {q : Projectivization ℂ (Fin (m + 1) → ℂ)} (hp : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p) (hq : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j q) :
    ComplexPoints.Analytic.ProjectiveCharts.projectiveChart (i, j) (segre p q) =
      finAffineSegre i j (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i p,
        ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart j q) := by
  have h := projectiveChart_segre i j (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i p, ComplexPoints.Analytic.ProjectiveCharts.projectiveChart j q)
  rw [(ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).left_inv hp, (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart j).left_inv hq] at h
  simpa only [finAffineSegre, expandFin_projectiveFinChart] using h

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre
