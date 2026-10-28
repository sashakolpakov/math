import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex

/-! # Smooth Cech Refinement -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechRefinement

noncomputable section

/-!
# Refinement of the actual smooth Čech–de Rham bicomplex

Every map below is restriction of genuine smooth sections along an inclusion
of open intersections. The maps respect both differentials, compose under
successive refinements, and preserve the actual restriction augmentation.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u

section Presheaves

variable {X ι κ ν : Type u} [TopologicalSpace X]
variable {F G : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ}
variable (U : ι → Opens X) (V : κ → Opens X) (r : κ → ι) (hr : ∀ k, V k ≤ U (r k))

/-- A refinement commutes with every morphism of the coefficient presheaves. -/
theorem cechCoefficientMap_refinement (α : F ⟶ G) (n : ℕ) (c : SmoothCech.CechCochain F U n) :
    SmoothCechDoubleComplex.cechCoefficientMap V α n (SmoothCech.cechRefinementMap F U V r hr n c) =
      SmoothCech.cechRefinementMap G U V r hr n (SmoothCechDoubleComplex.cechCoefficientMap U α n c) := by
  funext a
  change (α.app (op (SmoothCech.cechIntersection V a))).hom
      ((F.map (homOfLE (SmoothCech.cechIntersection_refinement_le U V r hr a)).op).hom
        (c (r ∘ a))) =
    (G.map (homOfLE (SmoothCech.cechIntersection_refinement_le U V r hr a)).op).hom
      ((α.app (op (SmoothCech.cechIntersection U (r ∘ a)))).hom (c (r ∘ a)))
  exact congrArg (fun f => f.hom (c (r ∘ a)))
    (α.naturality (homOfLE (SmoothCech.cechIntersection_refinement_le U V r hr a)).op)

/-- The identity refinement is the identity on actual Čech cochains. -/
theorem cechRefinementMap_id (n : ℕ) (c : SmoothCech.CechCochain F U n) :
    SmoothCech.cechRefinementMap F U U id (fun _ => le_refl _) n c = c := by
  funext a
  change (F.map (homOfLE (SmoothCech.cechIntersection_refinement_le U U id
    (fun _ => le_refl _) a)).op).hom (c a) = c a
  rw [show (homOfLE (SmoothCech.cechIntersection_refinement_le U U id
    (fun _ => le_refl _) a)).op = 𝟙 (op (SmoothCech.cechIntersection U a)) from Subsingleton.elim _ _]
  exact congrArg (fun f => f.hom (c a)) (F.map_id (op (SmoothCech.cechIntersection U a)))

/-- Successive restrictions equal the restriction for the composite refinement. -/
theorem cechRefinementMap_comp (W : ν → Opens X) (s : ν → κ)
    (hs : ∀ l, W l ≤ V (s l)) (n : ℕ) (c : SmoothCech.CechCochain F U n) :
    SmoothCech.cechRefinementMap F V W s hs n (SmoothCech.cechRefinementMap F U V r hr n c) =
      SmoothCech.cechRefinementMap F U W (r ∘ s) (fun l => (hs l).trans (hr (s l))) n c := by
  funext a
  change (F.map (homOfLE (SmoothCech.cechIntersection_refinement_le V W s hs a)).op).hom
      ((F.map (homOfLE (SmoothCech.cechIntersection_refinement_le U V r hr (s ∘ a))).op).hom
        (c (r ∘ s ∘ a))) =
    (F.map (homOfLE (SmoothCech.cechIntersection_refinement_le U W (r ∘ s)
      (fun l => (hs l).trans (hr (s l))) a)).op).hom (c (r ∘ s ∘ a))
  exact SmoothCech.cechSection_restrict_trans F _ _ _

end Presheaves

variable {E ι κ ν : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : ι → Opens E) (V : κ → Opens E) (r : κ → ι) (hr : ∀ k, V k ≤ U (r k))

/-- Exterior differentiation commutes with the actual refinement restriction. -/
theorem smoothCechExteriorD_refinement (p n : ℕ) (c : SmoothCech.SmoothCechCochain U p n) :
    SmoothCechDoubleComplex.smoothCechExteriorD V p n (SmoothCech.cechRefinementMap (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) U V r hr n c) =
      SmoothCech.cechRefinementMap (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E (p + 1)) U V r hr n
        (SmoothCechDoubleComplex.smoothCechExteriorD U p n c) :=
  cechCoefficientMap_refinement U V r hr (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheafD E p) n c

/-- Restriction on a refinement gives a map of the actual de Rham columns. -/
def smoothCechColumnRefinement (n : ℕ) : SmoothCechDoubleComplex.smoothCechColumn U n ⟶ SmoothCechDoubleComplex.smoothCechColumn V n :=
  CochainComplex.ofHom
    (fun p => ModuleCat.ofHom (SmoothCech.cechRefinementMap (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) U V r hr n))
    (fun p => by
      rw [SmoothCechDoubleComplex.smoothCechColumn_d, SmoothCechDoubleComplex.smoothCechColumn_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact smoothCechExteriorD_refinement U V r hr p n c)

@[simp]
theorem smoothCechColumnRefinement_f (n p : ℕ) :
    (smoothCechColumnRefinement U V r hr n).f p =
      ModuleCat.ofHom (SmoothCech.cechRefinementMap (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) U V r hr n) := rfl

/-- A genuine cover refinement induces a morphism of the entire smooth bicomplex. -/
def smoothCechDoubleComplexRefinement : SmoothCechDoubleComplex.smoothCechDoubleComplex U ⟶ SmoothCechDoubleComplex.smoothCechDoubleComplex V :=
  CochainComplex.ofHom (smoothCechColumnRefinement U V r hr)
    (fun n => by
      apply HomologicalComplex.Hom.ext
      funext p
      change (smoothCechColumnRefinement U V r hr n).f p ≫
          ((SmoothCechDoubleComplex.smoothCechDoubleComplex V).d n (n + 1)).f p =
        ((SmoothCechDoubleComplex.smoothCechDoubleComplex U).d n (n + 1)).f p ≫
          (smoothCechColumnRefinement U V r hr (n + 1)).f p
      rw [SmoothCechDoubleComplex.smoothCechDoubleComplex_d_f, SmoothCechDoubleComplex.smoothCechDoubleComplex_d_f,
        smoothCechColumnRefinement_f, smoothCechColumnRefinement_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact (SmoothCech.cechRefinementMap_delta (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) U V r hr n c).symm)

@[simp]
theorem smoothCechDoubleComplexRefinement_f_f (n p : ℕ) :
    ((smoothCechDoubleComplexRefinement U V r hr).f n).f p =
      ModuleCat.ofHom (SmoothCech.cechRefinementMap (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) U V r hr n) := rfl

/-- Refinement by the identity leaves the bicomplex unchanged. -/
theorem smoothCechDoubleComplexRefinement_id :
    smoothCechDoubleComplexRefinement U U id (fun _ => le_refl _) =
      𝟙 (SmoothCechDoubleComplex.smoothCechDoubleComplex U) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact cechRefinementMap_id U n c

/-- The bicomplex maps respect composition of refinements. -/
theorem smoothCechDoubleComplexRefinement_comp (W : ν → Opens E) (s : ν → κ)
    (hs : ∀ l, W l ≤ V (s l)) :
    smoothCechDoubleComplexRefinement U V r hr ≫ smoothCechDoubleComplexRefinement V W s hs =
      smoothCechDoubleComplexRefinement U W (r ∘ s) (fun l => (hs l).trans (hr (s l))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact cechRefinementMap_comp U V r hr W s hs n c

/-- Refinement preserves the actual restriction augmentation from open de Rham forms. -/
theorem smoothCechColumnAugmentation_refinement (W : Opens E) (hU : ∀ i, U i ≤ W) :
    SmoothCechDoubleComplex.smoothCechColumnAugmentation U W hU ≫ smoothCechColumnRefinement U V r hr 0 =
      SmoothCechDoubleComplex.smoothCechColumnAugmentation V W (fun k => (hr k).trans (hU (r k))) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  funext a
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechRefinement
