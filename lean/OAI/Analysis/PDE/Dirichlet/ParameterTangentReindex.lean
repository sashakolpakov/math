import OAI.Analysis.PDE.Dirichlet.NonlinearParameterJetReindex

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {Z E W : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The tangent space of a spatial halfspace in the enlarged ambient space
is exactly the product of all parameter directions and the spatial
tangent space. -/
def reindexTangentEquiv (e : W ≃L[ℝ] Z × E) (k : E →L[ℝ] ℝ) :
    (k.comp (reindexSpatialProjection e)).ker ≃L[ℝ] Z × k.ker where
  toFun u := ((e u).1,⟨(e u).2,u.property⟩)
  invFun u := ⟨e.symm (u.1,(u.2:E)),by
    change k ((e (e.symm (u.1,(u.2:E)))).2) = 0
    rw [e.apply_symm_apply]
    exact u.2.property⟩
  left_inv u := by
    apply Subtype.ext
    exact e.symm_apply_apply u
  right_inv u := by
    apply Prod.ext
    · exact congrArg (fun p : Z × E => p.1) (e.apply_symm_apply (u.1,(u.2:E)))
    · apply Subtype.ext
      exact congrArg (fun p : Z × E => p.2) (e.apply_symm_apply (u.1,(u.2:E)))
  map_add' u v := by
    apply Prod.ext
    · exact congrArg (fun p : Z × E => p.1) (map_add e (u:W) (v:W))
    · apply Subtype.ext
      exact congrArg (fun p : Z × E => p.2) (map_add e (u:W) (v:W))
  map_smul' a u := by
    apply Prod.ext
    · exact congrArg (fun p : Z × E => p.1) (map_smul e a (u:W))
    · apply Subtype.ext
      exact congrArg (fun p : Z × E => p.2) (map_smul e a (u:W))
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem reindexTangentEquiv_fst
    (e : W ≃L[ℝ] Z × E) (k : E →L[ℝ] ℝ)
    (v : (k.comp (reindexSpatialProjection e)).ker) :
    (reindexTangentEquiv e k v).1 = (e v).1 := rfl

@[simp] theorem reindexTangentEquiv_snd
    (e : W ≃L[ℝ] Z × E) (k : E →L[ℝ] ℝ)
    (v : (k.comp (reindexSpatialProjection e)).ker) :
    ((reindexTangentEquiv e k v).2:E) = (e v).2 := rfl

theorem reindexTangentEquiv_translation
    (e : W ≃L[ℝ] Z × E) (k : E →L[ℝ] ℝ) (w : W)
    (v : (k.comp (reindexSpatialProjection e)).ker) :
    e (w+(v:W)) = ((e w).1+(reindexTangentEquiv e k v).1,
      (e w).2+((reindexTangentEquiv e k v).2:E)) := by
  exact map_add e w (v:W)

end OAI.Analysis.PDE.Dirichlet
