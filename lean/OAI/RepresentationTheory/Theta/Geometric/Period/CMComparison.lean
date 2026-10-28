import OAI.RepresentationTheory.Theta.Geometric.Period.Comparison
import OAI.RepresentationTheory.Theta.Geometric.Period.Action
import OAI.RepresentationTheory.Theta.Geometric.Reference.Action

/-! # CM Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The diagonal CM action in the fixed quotient coordinates is the
actual integral action of every supplied reference fiber. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

variable {x : D.domain} (F : D.ReferenceAnalyticFiber x)

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.linearMap_ext_on_reference {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f g : Data.ActiveHeckeThetaData.referenceTangent (s := s) →ₗ[ℝ] W)
    (h : ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, f (F.periodEmbedding D v) = g (F.periodEmbedding D v)) : f = g := by
  have hs : Submodule.span ℝ (F.lattice : Set (Data.ActiveHeckeThetaData.referenceTangent (s := s))) = ⊤ := by
    let : CompactSpace ((Data.ActiveHeckeThetaData.referenceTangent (s := s)) ⧸ F.lattice.toIntSubmodule.toAddSubgroup) := F.compact
    exact CompactLattice.span_top_of_compact_quotient F.lattice.toIntSubmodule
  apply LinearMap.ext_on hs
  intro t ht
  obtain ⟨v, _, rfl⟩ := (F.lattice_membership t).mp ht
  exact h v

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.periodComparison_action (hg : D.pel.HasIntegralModelGeometry)
    (a : NumberField.RingOfIntegers E) (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    F.periodComparison D hg (D.periodScalarAction (a : E) t) =
      F.action a (F.periodComparison D hg t) := by
  let e := F.periodComparison D hg
  let f := ((e.toLinearMap.comp (D.periodScalarAction (a : E))).comp
    e.symm.toLinearMap).restrictScalars ℝ
  let g := (F.action a).restrictScalars ℝ
  have hfg : f = g := by
    apply F.linearMap_ext_on_reference D
    intro v
    have he : e.symm (F.periodEmbedding D v) =
        D.periodProjection x.val (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v) := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (F.periodComparison_projection D hg _).symm
    change e (D.periodScalarAction (a : E) (e.symm (F.periodEmbedding D v))) =
      F.action a (F.periodEmbedding D v)
    rw [he, ← D.periodProjection_ambientAction, F.periodComparison_projection,
      NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction_embedding]
    exact (F.equivariant a v).symm
  have ht := LinearMap.congr_fun hfg (e t)
  change e (D.periodScalarAction (a : E) (e.symm (e t))) = F.action a (e t) at ht
  simpa only [e.symm_apply_apply] using ht

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.action_bijective (hg : D.pel.HasIntegralModelGeometry)
    (a : NumberField.RingOfIntegers E) (ha : a ≠ 0) : Function.Bijective (F.action a) := by
  let e := F.periodComparison D hg
  have ha' : (a : E) ≠ 0 := by exact_mod_cast ha
  let f := e.symm.trans ((D.periodScalarEquiv (a : E) ha').trans e)
  have hf : ∀ t, f t = F.action a t := by
    intro t
    change e (D.periodScalarAction (a : E) (e.symm t)) = F.action a t
    rw [F.periodComparison_action, e.apply_symm_apply]
  exact (show Function.Bijective (fun t => F.action a t) by
    simpa only [← hf] using f.bijective)

end

end OAI.RepresentationTheory.Theta.Geometric
