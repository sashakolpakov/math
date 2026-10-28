import OAI.Analysis.PDE.Dirichlet.ParameterTangentReindex

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {Z E W F A B : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Reindexing by a linear equivalence commutes with every iterated
derivative, without a prior regularity hypothesis. -/
theorem iteratedFDeriv_linearEquiv_apply
    (L : A ≃L[ℝ] B) (f : B → F) (x : A) (N : ℕ) (v : Fin N → A) :
    iteratedFDeriv ℝ N (f ∘ L) x v =
      iteratedFDeriv ℝ N f (L x) (fun j => L (v j)) := by
  have h := L.iteratedFDerivWithin_comp_right f (s := univ)
    uniqueDiffOn_univ (x := x) (mem_univ _) N
  have hv := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin N => A) F => T v) h
  simpa only [preimage_univ,iteratedFDerivWithin_univ,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,ContinuousLinearEquiv.coe_coe] using hv

/-- Tangential derivatives in enlarged Euclidean coordinates are exactly
the mixed parameter/spatial-tangent derivatives. -/
theorem iteratedFDeriv_reindex_tangent
    (e : W ≃L[ℝ] Z × E) (k : E →L[ℝ] ℝ) (f : Z × E → F)
    (w : W) (N : ℕ) (v : Fin N → (k.comp (reindexSpatialProjection e)).ker) :
    iteratedFDeriv ℝ N (fun t : (k.comp (reindexSpatialProjection e)).ker =>
      f (e (w+(t:W)))) 0 v =
    iteratedFDeriv ℝ N (fun t : Z × k.ker =>
      f ((e w).1+t.1,(e w).2+(t.2:E))) 0 (fun j => reindexTangentEquiv e k (v j)) := by
  have he : (fun t : (k.comp (reindexSpatialProjection e)).ker => f (e (w+(t:W)))) =
      (fun t : Z × k.ker => f ((e w).1+t.1,(e w).2+(t.2:E))) ∘ reindexTangentEquiv e k := by
    funext t
    rw [reindexTangentEquiv_translation e k w t]
    rfl
  rw [he,iteratedFDeriv_linearEquiv_apply,map_zero]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- Agreement on a closed half-patch gives full germs in every tangent
direction, also at a boundary point. -/
theorem tangent_translation_germ_of_eqOn
    (ℓ : W →L[ℝ] ℝ) {O : Set W} (hO : IsOpen O)
    {f g : W → F} (he : EqOn g f ({x | 0 ≤ ℓ x} ∩ O))
    {w : W} (hw : w ∈ ({x | 0 ≤ ℓ x} ∩ O)) :
    (fun t : ℓ.ker => g (w+(t:W))) =ᶠ[𝓝 0] fun t : ℓ.ker => f (w+(t:W)) := by
  have hc : Continuous (fun t : ℓ.ker => w+(t:W)) := by fun_prop
  have hn : O ∈ 𝓝 (w+((0:ℓ.ker):W)) := by simpa using hO.mem_nhds hw.2
  filter_upwards [hc.continuousAt.tendsto.eventually hn] with t ht
  apply he ⟨?_,ht⟩
  have hz : ℓ (t:W) = 0 := t.property
  simpa only [Set.mem_ofPred_eq,map_add,hz,add_zero] using hw.1

/-- Transfer all mixed tangent jets to an actual extension on one fixed
half-patch. The extension need only agree on the half-patch itself. -/
theorem contDiffOn_tangent_jets_of_mixed_reindex
    (e : W ≃L[ℝ] Z × E) (k : E →L[ℝ] ℝ)
    {O : Set W} (hO : IsOpen O) {S : Set (Z × E)}
    {f : Z × E → F} {g : W → F}
    (he : EqOn g (f ∘ e) ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O))
    (hmaps : MapsTo e ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O) S)
    (hmixed : ∀ (N : ℕ) (v : Fin N → Z × k.ker),
      ContDiffOn ℝ 2 (fun p : Z × E => iteratedFDeriv ℝ N
        (fun t : Z × k.ker => f (p.1+t.1,p.2+(t.2:E))) 0 v) S) :
    ∀ (N : ℕ) (v : Fin N → (k.comp (reindexSpatialProjection e)).ker),
      ContDiffOn ℝ 2 (fun w => iteratedFDeriv ℝ N
        (fun t : (k.comp (reindexSpatialProjection e)).ker => g (w+(t:W))) 0 v)
        ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O) := by
  intro N v
  apply ((hmixed N (fun j => reindexTangentEquiv e k (v j))).comp
    e.contDiff.contDiffOn hmaps).congr
  intro w hw
  have hgerm := tangent_translation_germ_of_eqOn (k.comp (reindexSpatialProjection e)) hO he hw
  have hjet := congrArg (fun T : ContinuousMultilinearMap ℝ
    (fun _ : Fin N => (k.comp (reindexSpatialProjection e)).ker) F => T v)
    ((hgerm.iteratedFDeriv ℝ N).eq_of_nhds)
  exact hjet.trans (iteratedFDeriv_reindex_tangent e k f w N v)

end OAI.Analysis.PDE.Dirichlet
