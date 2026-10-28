import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.CoverRefinement
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DisjointSections
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.ExtensionSheaf

/-! # Extension Affine Cover -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology

noncomputable section

/-!
# GeometricComparison: actual affine covers trivializing cohomology torsors

Refine the torsor's own covering sieve by finitely many affine maps and
glue the local lifts over their disjoint union. The result is an affine
surjective cover carrying an actual torsor section.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} {F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (E : ExtensionOf.CohomologyExtension.Extension X F)

/-- Every affine site object has a single affine surjective cover with an actual torsor lift. -/
theorem ExtensionOf.CohomologyExtension.Extension.exists_affine_cover_lift (U : X.ProEt) [IsAffine U.left] :
    ∃ (T : X.ProEt) (g : T ⟶ U),
      IsAffine T.left ∧ Surjective g.left ∧ Nonempty (E.Fiber T) := by
  obtain ⟨V, hfin, hV⟩ := AlgebraicGeometry.FormalGeometry.Completion.Affine.CoverRefinement.Construction.proEtaleCoveringSieve_finiteAffineRefinement U
    (Presheaf.imageSieve E.projection.hom (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X U))
    (E.fiber_locally_nonempty U)
  have : Finite V.I₀ := hfin
  let Y := AlgebraicGeometry.FormalGeometry.Completion.Affine.CoverRefinement.Construction.affineRefinementSiteObject U V
  have (i : V.I₀) : IsAffine (Y i).left := inferInstanceAs (IsAffine (Spec (V.X i)))
  let p := AlgebraicGeometry.FormalGeometry.Completion.Affine.CoverRefinement.Construction.affineRefinementSiteMap U V
  have hsi (i : V.I₀) : Nonempty (E.Fiber (Y i)) := E.fiber_nonempty_of_imageSieve (p i) (hV i)
  obtain ⟨s, _, _⟩ := AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DisjointSections.Construction.proEtaleSheaf_disjoint_sections Y E.fiberSheaf
    (fun i => Classical.choice (hsi i))
  refine ⟨AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DisjointSections.Construction.proEtaleDisjointUnion Y, AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DisjointSections.Construction.proEtaleDisjointDesc Y p, ?_, ?_, ⟨s⟩⟩
  · change IsAffine (∐ (fun i => (Y i).left))
    infer_instance
  · constructor
    intro x
    obtain ⟨i, y, hy⟩ :=
      ((Scheme.presieve₀_mem_precoverage_iff (P := @WeaklyEtale.{u})
        V.cover.toPreZeroHypercover).mp V.cover.mem₀).1 x
    refine ⟨Sigma.ι (fun i => (Y i).left) i y, ?_⟩
    change (Sigma.desc (fun i => (p i).left)) (Sigma.ι (fun i => (Y i).left) i y) = x
    exact (congrArg (fun k : (Y i).left ⟶ U.left => k y)
      (Sigma.ι_comp_desc (fun i => (p i).left) i)).trans hy

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology
