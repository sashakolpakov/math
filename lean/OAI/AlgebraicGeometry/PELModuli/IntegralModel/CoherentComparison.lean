import OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuasicoherentPushforward
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentBinaryBiproduct
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Coherent Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentComparison

noncomputable section

/-! Coherent comparison spans extending actual isomorphisms on an open subset. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentBinaryBiproduct

universe u

def modulePullbackKernelIso {X : Scheme.{u}} {M N Q : X.Modules}
    (a : M ⟶ Q) (b : N ⟶ Q) :
    kernel (biprod.desc a (-b)) ≅ pullback a b :=
  limit.isoLimitCone ⟨_, Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct a b⟩

theorem modulePullback_quasicoherent {X : Scheme.{u}} {M N Q : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Q.IsQuasicoherent]
    (a : M ⟶ Q) (b : N ⟶ Q) : (pullback a b).IsQuasicoherent := by
  have : (M ⊞ N).IsQuasicoherent := SheafCohomology.Projective.CoherentBinaryBiproduct.module_biprod_quasicoherent M N
  exact (SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent X).prop_of_iso (modulePullbackKernelIso a b)
    (SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel (biprod.desc a (-b)))

theorem modulePullback_finiteType {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N Q : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Q.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType]
    (a : M ⟶ Q) (b : N ⟶ Q) : (pullback a b).IsFiniteType := by
  have : (M ⊞ N).IsQuasicoherent := SheafCohomology.Projective.CoherentBinaryBiproduct.module_biprod_quasicoherent M N
  have : (M ⊞ N).IsFiniteType := SheafCohomology.Projective.CoherentBinaryBiproduct.module_biprod_finiteType M N
  have := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_kernel (biprod.desc a (-b))
  exact SheafCohomology.Projective.FiniteTypeIso.finiteType_of_iso (modulePullbackKernelIso a b)

/-- The comparison is an actual fiber product inside the quasicoherent
direct image of one restriction. The two maps become isomorphisms on the
specified open subset and realize the supplied comparison there. -/
theorem exists_coherent_comparison_span
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) [QuasiCompact U.ι]
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    [M.IsFiniteType] [N.IsFiniteType]
    (e : M.restrict U.ι ≅ N.restrict U.ι) :
    ∃ (K : X.Modules) (a : K ⟶ M) (b : K ⟶ N),
      K.IsQuasicoherent ∧ K.IsFiniteType ∧
      IsIso ((restrictFunctor U.ι).map a) ∧
      IsIso ((restrictFunctor U.ι).map b) ∧
      (restrictFunctor U.ι).map a ≫ e.hom = (restrictFunctor U.ι).map b := by
  let F := restrictFunctor U.ι
  let G := pushforward U.ι
  let adj := restrictAdjunction U.ι
  let Q := G.obj (F.obj N)
  let a : M ⟶ Q := adj.unit.app M ≫ G.map e.hom
  let b : N ⟶ Q := adj.unit.app N
  have : Q.IsQuasicoherent :=
    QuasicoherentPushforward.quasicoherent_pushforward_of_quasiCompact_separated U.ι (F.obj N)
  have ha : IsIso (F.map a) := by
    dsimp only [a]
    rw [F.map_comp]
    infer_instance
  have hb : IsIso (F.map b) := by
    dsimp only [b, F, adj]
    infer_instance
  have : PreservesLimits F := SheafCohomology.Projective.ModuleRestrictLimits.Scheme.Modules.restrictFunctor_preservesLimits U.ι
  have hsquare := (IsPullback.of_hasPullback a b).map F
  refine ⟨pullback a b, pullback.fst a b, pullback.snd a b,
    modulePullback_quasicoherent a b, modulePullback_finiteType a b,
    hsquare.isIso_fst_of_isIso, hsquare.isIso_snd_of_isIso, ?_⟩
  have ha' : F.map a ≫ adj.counit.app (F.obj N) = e.hom := by
    dsimp only [a]
    rw [F.map_comp, Category.assoc]
    change F.map (adj.unit.app M) ≫ (G ⋙ F).map e.hom ≫
      adj.counit.app (F.obj N) = e.hom
    rw [adj.counit.naturality]
    change F.map (adj.unit.app M) ≫ adj.counit.app (F.obj M) ≫ e.hom = e.hom
    have ht : F.map (adj.unit.app M) ≫ adj.counit.app (F.obj M) = 𝟙 _ :=
      adj.left_triangle_components M
    rw [← Category.assoc, ht, Category.id_comp]
  have hb' : F.map b ≫ adj.counit.app (F.obj N) = 𝟙 _ :=
    adj.left_triangle_components N
  have h := congrArg (fun t => t ≫ adj.counit.app (F.obj N)) hsquare.w
  simpa only [Category.assoc, ha', hb', Category.comp_id] using h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentComparison
