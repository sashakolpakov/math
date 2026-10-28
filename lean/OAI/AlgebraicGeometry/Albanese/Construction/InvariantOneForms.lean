import OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed

/-! # Invariant One Forms -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.InvariantOneForms

noncomputable section

open scoped _root_.Manifold ContDiff _root_.Topology

open OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Group G] [TopologicalSpace G] [ChartedSpace F G]
  [LieGroup 𝓘(ℝ, F) ∞ G] [IsMulCommutative G]

/-- A one-covector is additive in its single tangent argument. -/
theorem oneCovector_add (α : F [⋀^Fin 1]→L[ℝ] ℂ) (v w : F) :
    α (fun _ => v + w) = α (fun _ => v) + α (fun _ => w) :=
  ((ContinuousAlternatingMap.ofSubsingleton ℝ F ℂ (0 : Fin 1)).symm α).map_add v w

omit [IsMulCommutative G] in
/-- Translation invariance evaluated on one tangent vector. -/
theorem invariantOneForm_translate (form : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := F) (G := G) 1)
    (a b : G) (v : F) :
    form.val (a * b) (fun _ => mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z : G => a * z) b v) =
      form.val b (fun _ => v) :=
  congrArg (fun η : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F G 1 => η b (fun _ => v))
    ((AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.mem_invariantForms_iff form.val).mp form.property a)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of an invariant one-form converts multiplication of maps into
addition of forms. Commutativity supplies invariance under right translations. -/
theorem invariantOneForm_pullback_mul (form : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := F) (G := G) 1)
    (g h : M → G) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (hh : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ h) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun x => g x * h x) (hg.mul hh) form.val =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg form.val + Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback h hh form.val := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  have hv : v = fun _ => v 0 := funext (fun i => congrArg v (Subsingleton.elim i 0))
  rw [hv]
  have hgd := hg.mdifferentiableAt (x := x) (by simp)
  have hhd := hh.mdifferentiableAt (x := x) (by simp)
  have hmd := (contMDiff_mul 𝓘(ℝ, F) ∞).mdifferentiableAt (x := (g x, h x)) (by simp)
  have hchain := mfderiv_comp (I := 𝓘(ℝ, E))
    (I' := 𝓘(ℝ, F).prod 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, F)) x hmd (hgd.prodMk hhd)
  rw [mfderiv_prodMk hgd hhd] at hchain
  have hder := congrArg (fun D : E →L[ℝ] F => D (v 0)) hchain
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun x => g x * h x) x (v 0) =
    mfderiv (𝓘(ℝ, F).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) (fun p : G × G => p.1 * p.2)
      (g x, h x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x (v 0),
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) h x (v 0)) at hder
  rw [mfderiv_prod_eq_add_apply hmd] at hder
  dsimp only at hder
  change form.val (g x * h x)
      (fun _ => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun x => g x * h x) x (v 0)) =
    form.val (g x) (fun _ => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x (v 0)) +
    form.val (h x) (fun _ => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) h x (v 0))
  apply (congrArg (fun w : F => form.val (g x * h x) (fun _ => w)) hder).trans
  apply (oneCovector_add (F := F) (form.val (g x * h x)) _ _).trans
  have hright : (fun z : G => z * h x) = fun z => h x * z := funext (fun z => mul_comm' z _)
  rw [hright]
  have hleft := invariantOneForm_translate form (h x) (g x)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x (v 0))
  rw [mul_comm' (h x) (g x)] at hleft
  exact congrArg₂ (· + ·) hleft (invariantOneForm_translate form (g x) (h x)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) h x (v 0)))

/-- Vanishing pullbacks remain zero after multiplication. -/
theorem invariantOneForm_pullback_mul_zero (form : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := F) (G := G) 1)
    (g h : M → G) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (hh : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ h)
    (hgz : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg form.val = 0)
    (hhz : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback h hh form.val = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun x => g x * h x) (hg.mul hh) form.val = 0 := by
  rw [invariantOneForm_pullback_mul form g h hg hh, hgz, hhz, add_zero]

/-- Vanishing pullbacks remain zero after inversion. -/
theorem invariantOneForm_pullback_inv_zero (form : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := F) (G := G) 1)
    (g : M → G) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (hgz : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg form.val = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun x => (g x)⁻¹) hg.inv form.val = 0 := by
  have hcomp := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp g hg (Inv.inv : G → G)
    (contMDiff_inv (I := 𝓘(ℝ, F)) (n := ∞)) form.val
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun x => (g x)⁻¹) hg.inv form.val = _ at hcomp
  rw [hcomp, AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.inv_pullback_invariant _ form.property, map_smul, hgz, smul_zero]

end

end OAI.AlgebraicGeometry.Albanese.Construction.InvariantOneForms
