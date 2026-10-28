import OAI.Geometry.ComplexTorus.RiemannProjectivity.FormsEq
import OAI.Geometry.ComplexTorus.RiemannProjectivity.PrimitiveEq
import OAI.AlgebraicTopology.DeRham.Comparison.RadialOne
import OAI.Analysis.DifferentialForms.Manifold.ClassRepresentatives

/-! # Torus Cohomology -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.TorusCohomology.Constructions.Torus

noncomputable section

/-!
# RiemannProjectivity: first cohomology of the period torus

This file works with pullback to the actual vector-space cover. All forms,
their differentials, and their cohomology classes are the existing geometric
objects; no cohomology comparison is supplied as a hypothesis.
-/

open scoped _root_.NumberField ContDiff _root_.Manifold _root_.Topology
open Filter

open OAI.Geometry.ComplexTorus.RiemannProjectivity.FormsEq.Constructions.Forms

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) {n : ℕ}

/-- Express an actual torus tangent covector in the common period coordinates. -/
def coefficient (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n)
    (p : Φ.periodTorus) : Analysis.DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n :=
  (form p).compContinuousLinearMap
    (Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv (Φ.periodChart p) (Φ.periodChart_mem_atlas p)
      p (Φ.mem_periodChart_source p)).symm.toContinuousLinearMap

/-- Pull a smooth torus form to the genuine vector-space cover. -/
def coverForm (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n :=
  (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback
    (QuotientAddGroup.mk : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Φ.periodTorus)
    (FormsEq.Constructions.Forms.projection_real_smooth Φ) form).toNormedSpace

theorem coverForm_apply (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n)
    (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :
    coverForm Φ form z = coefficient Φ form (QuotientAddGroup.mk z) := by
  ext v
  apply congrArg (form (QuotientAddGroup.mk z))
  funext i
  apply (Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv (Φ.periodChart (QuotientAddGroup.mk z))
    (Φ.periodChart_mem_atlas _) _ (Φ.mem_periodChart_source _)).injective
  exact (congrArg (fun L : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E => L (v i))
    (FormsEq.Constructions.Forms.projection_tangent_identity Φ z)).trans
      ((Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv (Φ.periodChart (QuotientAddGroup.mk z))
        (Φ.periodChart_mem_atlas _) _ (Φ.mem_periodChart_source _)).apply_symm_apply (v i)).symm

/-- Coefficients of a lifted form are periodic under the original lattice. -/
theorem coverForm_periodic (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n)
    (z t : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (ht : t ∈ Φ.periodIntegerLattice) :
    coverForm Φ form (z + t) = coverForm Φ form z := by
  rw [coverForm_apply, coverForm_apply, QuotientAddGroup.mk_add,
    (QuotientAddGroup.eq_zero_iff t).mpr ht, add_zero]

/-- A form is determined by its pullback to the covering vector space. -/
theorem coverForm_injective : Function.Injective
    (coverForm Φ : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n →
      Analysis.DifferentialForms.Manifold.Basic.SmoothForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n) := by
  intro a b hab
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro p
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective p
  have h := congrArg (fun f : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n => f z) hab
  rw [coverForm_apply, coverForm_apply] at h
  ext v
  let e := Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv (Φ.periodChart (QuotientAddGroup.mk z))
    (Φ.periodChart_mem_atlas _) _ (Φ.mem_periodChart_source _)
  have hv := congrArg (fun f : Analysis.DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) n => f (fun i => e (v i))) h
  simpa only [coefficient, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, Function.comp_def, e,
    ContinuousLinearEquiv.symm_apply_apply] using hv

theorem coverForm_d (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n) :
    coverForm Φ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) = Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (coverForm Φ form) := by
  unfold coverForm
  rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.toNormedSpace_d]

theorem coverForm_sub (a b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n) :
    coverForm Φ (a - b) = coverForm Φ a - coverForm Φ b := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro z
  ext v
  rfl

/-- Descent of a lattice-periodic scalar function through the actual quotient. -/
def descendFunction (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ)
    (hF : ∀ z t, t ∈ Φ.periodIntegerLattice → F (z + t) = F z) : Φ.periodTorus → ℂ :=
  Quotient.lift F (by
    intro z w hzw
    have ht : -z + w ∈ Φ.periodIntegerLattice := QuotientAddGroup.leftRel_apply.mp hzw
    have h := hF z (-z + w) ht
    simpa using h.symm)

@[simp]
theorem descendFunction_mk (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ)
    (hF : ∀ z t, t ∈ Φ.periodIntegerLattice → F (z + t) = F z)
    (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) : descendFunction Φ F hF (QuotientAddGroup.mk z) = F z := rfl

def descendedZeroRaw (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ)
    (hF : ∀ z t, t ∈ Φ.periodIntegerLattice → F (z + t) = F z) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 0 :=
  fun p => ContinuousAlternatingMap.constOfIsEmpty ℝ
    (TangentSpace 𝓘(ℝ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) p) (Fin 0) (descendFunction Φ F hF p)

/-- In a period chart, a descended zero-form is exactly the original function. -/
theorem descendedZeroRaw_inChart (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ)
    (hF : ∀ z t, t ∈ Φ.periodIntegerLattice → F (z + t) = F z)
    (p : Φ.periodTorus) :
    (descendedZeroRaw Φ F hF).inChart (Φ.periodChart p) =
      fun z => ContinuousAlternatingMap.constOfIsEmpty ℝ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (Fin 0) (F z) := by
  funext z
  ext v
  change descendFunction Φ F hF ((Φ.periodChart p).symm z) = F z
  rw [Φ.periodChart_symm]
  rfl

/-- Smooth periodic functions descend as genuine smooth manifold zero-forms. -/
def descendedZeroForm (F : Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E))
    (hF : ∀ z t, t ∈ Φ.periodIntegerLattice → F (z + t) = F z) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 0 :=
  ⟨descendedZeroRaw Φ F hF, by
    intro e he
    obtain ⟨p, rfl⟩ := he
    rw [descendedZeroRaw_inChart]
    exact F.toZeroForm.smooth.contDiffOn⟩

theorem coverForm_descendedZeroForm (F : Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E))
    (hF : ∀ z t, t ∈ Φ.periodIntegerLattice → F (z + t) = F z) :
    coverForm Φ (descendedZeroForm Φ F hF) = F.toZeroForm := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro z
  ext v
  rfl

/-- A closed one-form pulled to the vector-space cover has a global smooth
primitive, obtained by actual radial integration. -/
theorem exists_cover_primitive
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1) :
    ∃ F : Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E), ∀ z,
      HasFDerivAt (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ)
        (AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (coverForm Φ a.val) z) z := by
  let g := coverForm Φ a.val
  have hgclosed : ∀ z, extDeriv (g : Analysis.DifferentialForms.Manifold.Basic.RawForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 1) z = 0 := by
    have hd : Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d g = 0 := by
      rw [← coverForm_d, a.property]
      rfl
    exact fun z => congrArg (fun f : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 2 => f z) hd
  have hPsmooth : ContDiff ℝ ∞ (AlgebraicTopology.DeRham.Comparison.RadialOne.radialPrimitive
      (AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (g : Analysis.DifferentialForms.Manifold.Basic.RawForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 1))) := by
    exact contDiffOn_univ.mp (AlgebraicTopology.DeRham.Comparison.RadialOne.contDiffOn_radialPrimitive_of_closed_star
      (starConvex_univ 0) isOpen_univ g.smooth.contDiffOn (fun z _ => hgclosed z))
  refine ⟨⟨_, hPsmooth⟩, ?_⟩
  intro z
  exact AlgebraicTopology.DeRham.Comparison.RadialOne.hasFDerivAt_radialPrimitive convex_univ isOpen_univ (Set.mem_univ 0)
    (AlgebraicTopology.DeRham.Comparison.RadialOne.differentiableOn_altOneFormToLinear (g.smooth.differentiable (by simp)).differentiableOn)
    (fun y _ => AlgebraicTopology.DeRham.Comparison.RadialOne.symmetric_fderiv_altOneFormToLinear (hgclosed y)) (Set.mem_univ z)

/-- Every closed one-form differs from an invariant one-form by the
derivative of a genuine smooth function on the quotient. -/
theorem closed_oneForm_eq_invariant_mod_exact
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1) :
    ∃ (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ)
      (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 0),
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = a.val - (FormsEq.Constructions.Forms.invariantClosedOneForm Φ l).val := by
  obtain ⟨F, hF⟩ := exists_cover_primitive Φ a
  have hperiod : ∀ z t, t ∈ Φ.periodIntegerLattice →
      fderiv ℝ (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ) (z + t) = fderiv ℝ (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ) z := by
    intro z t ht
    rw [(hF (z + t)).fderiv, (hF z).fderiv]
    unfold AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear
    rw [coverForm_periodic Φ a.val z t ht]
  obtain ⟨l, _, hrem⟩ := PrimitiveEq.Constructions.Primitive.exists_periodic_remainder Φ.periodIntegerLattice
    (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ) (F.smooth.differentiable (by simp)) hperiod
  let G : Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) := ⟨fun z => F z - l z, F.smooth.sub l.contDiff⟩
  have hG : ∀ z t, t ∈ Φ.periodIntegerLattice → G (z + t) = G z := hrem
  refine ⟨l, descendedZeroForm Φ G hG, ?_⟩
  apply coverForm_injective Φ
  rw [coverForm_d, coverForm_descendedZeroForm, coverForm_sub]
  change Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d G.toZeroForm = coverForm Φ a.val -
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback
      (QuotientAddGroup.mk : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Φ.periodTorus)
      (FormsEq.Constructions.Forms.projection_real_smooth Φ) (FormsEq.Constructions.Forms.invariantForm Φ
        (ContinuousAlternatingMap.ofSubsingleton ℝ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) ℂ (0 : Fin 1) l))).toNormedSpace
  rw [FormsEq.Constructions.Forms.invariantForm_pullback]
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro z
  ext v
  have hdG : HasFDerivAt (G : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ)
      (AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (coverForm Φ a.val) z - l) z :=
    (hF z).sub l.hasFDerivAt
  rw [Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.d_toZeroForm_apply, hdG.fderiv]
  change AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (coverForm Φ a.val) z (v 0) - l (v 0) =
    coverForm Φ a.val z v - l (v 0)
  congr 1
  exact congrArg (fun form : Analysis.DifferentialForms.Manifold.Basic.RawForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 1 => form z v)
    (AlgebraicTopology.DeRham.Comparison.RadialOne.linearOneFormToAlt_altOneFormToLinear (coverForm Φ a.val))

/-- Every first de Rham class is represented by an invariant covector. -/
theorem invariantH1_surjective : Function.Surjective (FormsEq.Constructions.Forms.invariantH1 Φ) := by
  intro h
  obtain ⟨a, rfl⟩ := Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamFormClass_surjective (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 h
  obtain ⟨l, f, hf⟩ := closed_oneForm_eq_invariant_mod_exact Φ a
  refine ⟨l, ?_⟩
  have hzero : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1
      (a - FormsEq.Constructions.Forms.invariantClosedOneForm Φ l) = 0 :=
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 _).mpr ⟨f, hf⟩
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero.symm

/-- Actual first de Rham cohomology of the period torus is the complex
space of real-linear covectors on its covering vector space. -/
def invariantH1Equiv : (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) ≃ₗ[ℂ]
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 :=
  LinearEquiv.ofBijective (FormsEq.Constructions.Forms.invariantH1 Φ)
    ⟨FormsEq.Constructions.Forms.invariantH1_injective Φ, invariantH1_surjective Φ⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.TorusCohomology.Constructions.Torus
