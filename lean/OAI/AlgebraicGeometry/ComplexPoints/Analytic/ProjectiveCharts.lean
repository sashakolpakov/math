import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCompactness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Projective Charts -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts

noncomputable section

/-!
# The standard affine charts of complex projective space

The underlying space is mathlib's quotient of nonzero homogeneous coordinate
vectors. Its topology is the ordinary quotient topology, and the coordinate
maps below are the representative-independent ratios defined in
`Algebraic.ProjectiveCoordinates`. Each standard patch is open and is
homeomorphic to the usual complex affine coordinate space.
-/

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {ι : Type*}

/-- A standard nonvanishing-coordinate patch is open in the ordinary quotient
topology of complex projective space. -/
theorem isOpen_projectivePatch (i : ι) :
    IsOpen {p : Projectivization ℂ (ι → ℂ) | Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p} := by
  rw [ProjectiveCompactness.isOpen_projectivization_iff]
  simpa only [Set.preimage_ofPred_eq, Projectivization.mk'_eq_mk,
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff] using
    (isOpen_ne_fun ((continuous_apply i).comp continuous_subtype_val)
      continuous_const :
      IsOpen {v : {v : ι → ℂ // v ≠ 0} | v.val i ≠ 0})

/-- The ratio of homogeneous coordinates is continuous wherever its denominator
coordinate is nonzero. -/
theorem continuousOn_projectiveRatio (i j : ι) :
    ContinuousOn (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j : Projectivization ℂ (ι → ℂ) → ℂ)
      {p | Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p} := by
  apply (Topology.IsQuotientMap.continuousOn_isOpen_iff
    (ProjectiveCompactness.isQuotientMap_projectivization_mk' ℂ (ι → ℂ))
    (g := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j) (isOpen_projectivePatch i)).mpr
  change ContinuousOn
    (fun v : {v : ι → ℂ // v ≠ 0} => v.val j / v.val i)
    {v | Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (Projectivization.mk' ℂ v)}
  apply (((continuous_apply j).comp continuous_subtype_val).continuousOn).div
    (((continuous_apply i).comp continuous_subtype_val).continuousOn)
  intro v hv
  exact (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i v.val v.property).mp hv

/-- Continuity of the ordinary affine chart on its open projective patch. -/
theorem continuous_projectiveAffineChart (i : ι) :
    Continuous (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.affineChart (K := ℂ) i) := by
  apply continuous_pi
  intro j
  exact (continuousOn_projectiveRatio i j.val).domRestrict

/-- The inverse affine chart continuously inserts the normalized coordinate 1
and projects the resulting nonzero vector to its projective line. -/
theorem continuous_projectiveAffineChart_symm (i : ι) :
    Continuous (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.affineChart (K := ℂ) i).symm := by
  classical
  apply continuous_induced_rng.mpr
  change Continuous (fun f : {j : ι // j ≠ i} → ℂ =>
    Projectivization.mk ℂ (fun j => if h : j = i then 1 else f ⟨j, h⟩) _)
  have hc : Continuous (fun f : {j : ι // j ≠ i} → ℂ =>
      fun j => if h : j = i then (1 : ℂ) else f ⟨j, h⟩) := by
    apply continuous_pi
    intro j
    by_cases h : j = i
    · simpa [h] using
        (continuous_const : Continuous (fun _ : {j : ι // j ≠ i} → ℂ => (1 : ℂ)))
    · simpa [h] using
        (continuous_apply (⟨j, h⟩ : {j : ι // j ≠ i}))
  exact (ProjectiveCompactness.continuous_projectivization_mk' ℂ (ι → ℂ)).comp
    (hc.subtype_mk _)

/-- The standard affine chart as a homeomorphism for the ordinary topology. -/
def projectiveAffineChart (i : ι) :
    {p : Projectivization ℂ (ι → ℂ) // Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p} ≃ₜ
      ({j : ι // j ≠ i} → ℂ) where
  toEquiv := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.affineChart i
  continuous_toFun := continuous_projectiveAffineChart i
  continuous_invFun := continuous_projectiveAffineChart_symm i

@[simp]
theorem projectiveAffineChart_apply (i : ι)
    (p : {p : Projectivization ℂ (ι → ℂ) // Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p})
    (j : {j : ι // j ≠ i}) :
    projectiveAffineChart i p j = Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j.val p.val := rfl

/-- The standard affine chart as an open partial homeomorphism defined on the
full projective space. Its source is the nonvanishing-coordinate patch and its
target is the whole affine coordinate space. -/
def projectiveChart (i : ι) :
    OpenPartialHomeomorph (Projectivization ℂ (ι → ℂ)) ({j : ι // j ≠ i} → ℂ) where
  toFun p j := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j.val p
  invFun z := ((projectiveAffineChart i).symm z).val
  source := {p | Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p}
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' z _ := ((projectiveAffineChart i).symm z).property
  left_inv' p hp := congrArg Subtype.val
    ((projectiveAffineChart i).symm_apply_apply ⟨p, hp⟩)
  right_inv' z _ := (projectiveAffineChart i).apply_symm_apply z
  open_source := isOpen_projectivePatch i
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_pi.mpr fun j => continuousOn_projectiveRatio i j.val
  continuousOn_invFun :=
    (continuous_subtype_val.comp (projectiveAffineChart i).symm.continuous).continuousOn

@[simp]
theorem projectiveChart_source (i : ι) :
    (projectiveChart i).source = {p | Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p} := rfl

@[simp]
theorem projectiveChart_target (i : ι) :
    (projectiveChart i).target = Set.univ := rfl

@[simp]
theorem projectiveChart_apply (i : ι) (p : Projectivization ℂ (ι → ℂ))
    (j : {j : ι // j ≠ i}) : projectiveChart i p j = Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j.val p := rfl

/-- The affine model with the distinguished homogeneous coordinate removed is
the standard `Fin n` coordinate space. -/
def projectiveFinChart {n : ℕ} (i : Fin (n + 1)) :
    OpenPartialHomeomorph (Projectivization ℂ (Fin (n + 1) → ℂ)) (Fin n → ℂ) :=
  (projectiveChart i).transHomeomorph
    (Homeomorph.piCongrLeft (Y := fun _ : {j : Fin (n + 1) // j ≠ i} => ℂ)
      (finSuccAboveEquiv i)).symm

@[simp]
theorem projectiveFinChart_source {n : ℕ} (i : Fin (n + 1)) :
    (projectiveFinChart i).source = {p | Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p} := rfl

@[simp]
theorem projectiveFinChart_target {n : ℕ} (i : Fin (n + 1)) :
    (projectiveFinChart i).target = Set.univ := rfl

@[simp]
theorem projectiveFinChart_apply {n : ℕ} (i : Fin (n + 1))
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (j : Fin n) :
    projectiveFinChart i p j = Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i (i.succAbove j) p := rfl

/-- Every projective point belongs to the source of a standard finite-dimensional
affine chart. -/
theorem exists_mem_projectiveFinChart_source {n : ℕ}
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) :
    ∃ i, p ∈ (projectiveFinChart i).source :=
  Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch p

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts
