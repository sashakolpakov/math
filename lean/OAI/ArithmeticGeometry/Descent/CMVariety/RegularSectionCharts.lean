import OAI.ArithmeticGeometry.Descent.CMVariety.RegularRelativeCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.RelativePointOpenness
import OAI.ArithmeticGeometry.Descent.CMVariety.SectionCoordinates

/-! # Regular Section Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
Normalize a genuine algebraic section in actual smooth relative charts.
The neighborhood is obtained from continuity; analyticity of the section
coordinates follows from its algebra homomorphism and the regular chart
formulas. Inverse-chart evaluation of regular functions remains analytic.
-/

open Set
open scoped Classical ContDiff

variable {R A : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]

/-- A constructed neighborhood and relative chart in which the actual
algebraic section has zero fiber coordinate. -/
structure RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (s : A →ₐ[ℂ] R) where
  charts : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F)
  onSection : (x.comp (IsScalarTower.toAlgHom ℂ R A)).comp s = x
  neighborhood : Set F
  isOpen : IsOpen neighborhood
  center : charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A)) ∈ neighborhood
  withinBase : neighborhood ⊆ charts.base.target
  sectionPoint : ∀ z ∈ neighborhood,
    (charts.base.symm z).comp s ∈ charts.total.source
  sectionZero : ∀ z ∈ neighborhood,
    charts.total ((charts.base.symm z).comp s) = (z, 0)
  forwardTotal : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates charts.total

theorem SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts.normalizeSection
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A}
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F))
    (s : A →ₐ[ℂ] R)
    (hs : s.comp (IsScalarTower.toAlgHom ℂ R A) = AlgHom.id ℂ R)
    (hx : (x.comp (IsScalarTower.toAlgHom ℂ R A)).comp s = x)
    (hforward : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates C.total)
    (hcoord : ContDiffOn ℂ ω (fun z => C.total ((C.base.symm z).comp s))
      (C.base.target ∩ {z | (C.base.symm z).comp s ∈ C.total.source})) :
    Nonempty (RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x s) := by
  let f : F → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A := fun z => (C.base.symm z).comp s
  let U := C.base.target ∩ f ⁻¹' C.total.source
  have hf : ContinuousOn f C.base.target :=
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap s).continuous.continuousOn.comp
      C.base.symm.continuousOn (mapsTo_univ _ _)
  have hU : IsOpen U := hf.isOpen_inter_preimage C.base.open_target C.total.open_source
  have hbase (z : F) (hz : z ∈ U) : (C.total (f z)).1 = z := by
    have hp := C.projection (C.total (f z)) (C.total.map_source hz.2)
    rw [C.total.left_inv hz.2] at hp
    have hs' : (f z).comp (IsScalarTower.toAlgHom ℂ R A) = C.base.symm z := by
      change ((C.base.symm z).comp s).comp (IsScalarTower.toAlgHom ℂ R A) = _
      rw [AlgHom.comp_assoc, hs, AlgHom.comp_id]
    rw [hs', C.base.right_inv hz.1] at hp
    exact hp.symm
  let h : F → E := fun z => (C.total (f z)).2
  have hh : ContDiffOn ℂ ω h U := hcoord.snd
  let shift := SectionCoordinates.Abelian.sectionShift U hU h hh.continuousOn
  let en := C.total.trans shift
  have hsection (z : F) (hz : z ∈ U) :
      f z ∈ en.source ∧ en (f z) = (z, 0) := by
    constructor
    · refine ⟨hz.2, ?_⟩
      change (C.total (f z)).1 ∈ U ∧ (C.total (f z)).2 ∈ (univ : Set E)
      exact ⟨(hbase z hz).symm ▸ hz, mem_univ _⟩
    · change ((C.total (f z)).1,
        (C.total (f z)).2 - (C.total (f ((C.total (f z)).1))).2) = (z, 0)
      rw [hbase z hz, sub_self]
  let z₀ := C.base (x.comp (IsScalarTower.toAlgHom ℂ R A))
  have hf₀ : f z₀ = x := by
    change (C.base.symm (C.base (x.comp (IsScalarTower.toAlgHom ℂ R A)))).comp s = x
    rw [C.base.left_inv C.basePoint]
    exact hx
  have hz₀ : z₀ ∈ U :=
    ⟨C.base.map_source C.basePoint,
      (congrArg (fun y => y ∈ C.total.source) hf₀).mpr C.point⟩
  have hshift := (SectionCoordinates.Abelian.sectionShift_contDiffOn U hU h hh).2
  let Cn : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F) := {
    base := C.base
    total := en
    basePoint := C.basePoint
    point := (congrArg (fun y => y ∈ en.source) hf₀).mp (hsection z₀ hz₀).1
    mapsTo := fun z hz => C.mapsTo (shift.symm z) hz.2
    projection := fun z hz => C.projection (shift.symm z) hz.2
    regularTotal := fun a => (C.regularTotal a).comp
      (hshift.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
    regularBase := C.regularBase }
  exact ⟨{
    charts := Cn
    onSection := hx
    neighborhood := U
    isOpen := hU
    center := hz₀
    withinBase := inter_subset_left
    sectionPoint := fun z hz => (hsection z hz).1
    sectionZero := fun z hz => (hsection z hz).2
    forwardTotal := hforward.trans shift (SectionCoordinates.Abelian.sectionShift_contDiffOn U hU h hh).1 }⟩

theorem RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts.center_coordinates
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A} {s : A →ₐ[ℂ] R}
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x s) :
    N.charts.total x =
      (N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A)), 0) := by
  have h := N.sectionZero _ N.center
  rw [N.charts.base.left_inv N.charts.basePoint, N.onSection] at h
  exact h

/-- An actual smooth relative algebra with an actual algebraic section
has local analytic product charts that send that section to zero. All
chart and section-regularity data are constructed from the algebra maps. -/
theorem RegularSectionCharts.Abelian.RelativeCharts.exists_smooth_relative_section_charts
    {I Sigma : Type} [Fintype I] [Fintype Sigma]
    (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    [Algebra.Smooth R A] (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (s : A →ₐ[ℂ] R)
    (hs : s.comp (IsScalarTower.toAlgHom ℂ R A) = AlgHom.id ℂ R)
    (hx : (x.comp (IsScalarTower.toAlgHom ℂ R A)).comp s = x) :
    ∃ D : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.RelativePresentationAt (R := R) x,
      Nonempty (RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts
        (E := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates D.presentation.map → ℂ)
        (F := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) x s) := by
  obtain ⟨D, C, _, ht⟩ := RegularRelativeCharts.Abelian.RelativeCharts.exists_smooth_relative_regular_charts P x
  let e := ComposedSmoothCharts.Abelian.RelativeCharts.productCoordinates P D.presentation
  have he : (ComposedSmoothCharts.Abelian.RelativeCharts.baseProjection P D.presentation : _ → _) ∘ e.symm = Prod.fst := by
    funext z
    rw [Function.comp_apply, ← ComposedSmoothCharts.Abelian.RelativeCharts.productCoordinates_fst]
    exact congrArg Prod.fst (e.apply_symm_apply z)
  let Cp : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x
      (Prod.fst : (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) ×
        (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates D.presentation.map → ℂ) → (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ)) :=
    he ▸ C.changeCoordinates e
  have hcoord : ContDiffOn ℂ ω (fun z => Cp.total ((Cp.base.symm z).comp s))
      (Cp.base.target ∩ {z | (Cp.base.symm z).comp s ∈ Cp.total.source}) := by
    have h := ht.comap_contDiffOn s C.base C.regularBase
    exact e.contDiff.comp_contDiffOn h
  have hforward : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates Cp.total :=
    ht.hasAnalyticCoordinates.transHomeomorph e
  exact ⟨D, Cp.normalizeSection s hs hx hforward hcoord⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety
