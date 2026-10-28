import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverLocalM
import OAI.Analysis.DifferentialForms.Manifold.PurePullback

/-! # Cover Pure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverPure.CM

noncomputable section

/-! ThetaCycle: holomorphic covering pullback also detects pure bidegree.
Purity of a descended form is proved in the actual inverse covering charts. -/

open scoped Classical _root_.Manifold ContDiff
open Set

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ, E) ∞ M] [IsManifold 𝓘(ℂ, F) ∞ N]
  {p q : ℕ}

theorem pure_local_pullback_inChart (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q))
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q a) (g : N → M)
    (e : OpenPartialHomeomorph N F) (c : OpenPartialHomeomorph M E)
    (he : e ∈ atlas F N) (hc : c ∈ atlas E M) (y : F)
    (hy : y ∈ e.target) (hcy : g (e.symm y) ∈ c.source)
    (hg : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, E) ∞ g (e.symm y)) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree F p q ((a.pullback (E := F) g).inChart e y) := by
  rw [a.pullback_inChart g e c he hc hy hcy
    ((Analysis.DifferentialForms.Manifold.Holomorphic.contMDiffAt_real_of_complex hg).mdifferentiableAt (by simp))]
  have hd := (Analysis.DifferentialForms.Manifold.Holomorphic.complexContDiffAt_manifoldMap_inChart g e c he hc hy hcy hg).differentiableAt (by simp)
  rw [hd.fderiv_restrictScalars ℝ]
  exact AlgebraicTopology.DeRham.Comparison.BidegreeRestriction.hasBidegree_pullback (ha c hc (c (g (e.symm y))) (c.map_source hcy))
    (fderiv ℂ (c ∘ g ∘ e.symm) y)

theorem raw_form_pure_of_cover_pullback (f : M → N) (hs : Function.Surjective f)
    (hf : IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f)
    (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N (p + q))
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q (a.pullback (E := E) f)) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree F N p q a := by
  rw [Analysis.DifferentialForms.Manifold.BidegreeInvariant.hasManifoldBidegree_iff_chartAt]
  intro y
  obtain ⟨x, rfl⟩ := hs y
  obtain ⟨φ, hx, hφ⟩ := hf x
  have htarget : f x ∈ φ.target := by rw [hφ hx]; exact φ.map_source hx
  have hsection : ∀ y ∈ φ.target, f (φ.symm y) = y :=
    fun y hy => (hφ (φ.map_target hy)).trans (φ.right_inv hy)
  have hi : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ φ.symm φ.target := fun y hy =>
    (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiffAt_real_of_complex ((φ.contMDiffOn_invFun y hy).contMDiffAt
      (φ.open_target.mem_nhds hy))).contMDiffWithinAt
  have hvalue := CoverLocalM.CM.raw_pullback_local_section f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf.contMDiff)
    φ.symm φ.target φ.open_target hi hsection (p + q) a (f x) htarget
  let e := chartAt F (f x)
  let c := chartAt E (φ.symm (f x))
  have he : e ∈ atlas F N := chart_mem_atlas F (f x)
  have hc : c ∈ atlas E M := chart_mem_atlas E (φ.symm (f x))
  have hy : e (f x) ∈ e.target := mem_chart_target F (f x)
  have hey : e.symm (e (f x)) = f x := e.left_inv (mem_chart_source F (f x))
  have hcy : φ.symm (e.symm (e (f x))) ∈ c.source := by
    rw [hey]
    exact mem_chart_source E (φ.symm (f x))
  have hg : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, E) ∞ φ.symm (e.symm (e (f x))) := by
    rw [hey]
    exact (φ.contMDiffOn_invFun (f x) htarget).contMDiffAt (φ.open_target.mem_nhds htarget)
  have hp := pure_local_pullback_inChart (a.pullback (E := E) f) ha φ.symm e c he hc (e (f x)) hy hcy hg
  have heq : ((a.pullback (E := E) f).pullback φ.symm).inChart e (e (f x)) = a.inChart e (e (f x)) := by
    change (((a.pullback (E := E) f).pullback φ.symm) (e.symm (e (f x)))).compContinuousLinearMap _ =
      (a (e.symm (e (f x)))).compContinuousLinearMap _
    rw [hey, hvalue]
  rw [heq] at hp
  exact hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverPure.CM
