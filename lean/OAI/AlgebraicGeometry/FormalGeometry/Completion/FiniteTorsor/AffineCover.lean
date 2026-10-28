import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.CoverRefinement
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DisjointSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.TorsorSheaf

/-! # Affine Cover -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: actual affine covers trivializing finite torsors

Refine the torsor's own covering sieve by finitely many affine maps and
glue the local lifts over their disjoint union. The result is an affine
surjective cover carrying an actual torsor section.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {ℓ n : ℕ} {X : Scheme.{u}} (E : App.Construction.FiniteCoefficientExtension ℓ n X)

/-- Every affine site object has a single affine surjective cover with an actual torsor lift. -/
theorem App.Construction.FiniteCoefficientExtension.exists_affine_cover_lift (U : X.ProEt) [IsAffine U.left] :
    ∃ (T : X.ProEt) (g : T ⟶ U),
      IsAffine T.left ∧ Surjective g.left ∧ Nonempty (E.Fiber T) := by
  obtain ⟨V, hfin, hV⟩ := Affine.CoverRefinement.Construction.proEtaleCoveringSieve_finiteAffineRefinement U
    (Presheaf.imageSieve E.projection.hom (App.Construction.proEtIntegerLocalGenerator X U))
    (E.fiber_locally_nonempty U)
  have : Finite V.I₀ := hfin
  let Y := Affine.CoverRefinement.Construction.affineRefinementSiteObject U V
  have (i : V.I₀) : IsAffine (Y i).left := inferInstanceAs (IsAffine (Spec (V.X i)))
  let p := Affine.CoverRefinement.Construction.affineRefinementSiteMap U V
  have hsi (i : V.I₀) : Nonempty (E.Fiber (Y i)) := E.fiber_nonempty_of_imageSieve (p i) (hV i)
  obtain ⟨s, _, _⟩ := ProEtale.DisjointSections.Construction.proEtaleSheaf_disjoint_sections Y E.fiberSheaf
    (fun i => Classical.choice (hsi i))
  refine ⟨ProEtale.DisjointSections.Construction.proEtaleDisjointUnion Y, ProEtale.DisjointSections.Construction.proEtaleDisjointDesc Y p, ?_, ?_, ⟨s⟩⟩
  · change IsAffine (∐ (fun i => (Y i).left))
    infer_instance
  · constructor
    intro x
    obtain ⟨i, y, hy⟩ := V.cover.exists_eq x
    refine ⟨Sigma.ι (fun i => (Y i).left) i y, ?_⟩
    change (Sigma.desc (fun i => (p i).left)) (Sigma.ι (fun i => (Y i).left) i y) = x
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
    exact hy

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
