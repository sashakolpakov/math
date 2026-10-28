import OAI.Analysis.PDE.Elliptic.Boundary.Third.ChainRule

/-! Fourth derivatives under a fixed nonlinear coordinate change. -/

noncomputable section
open Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

local instance fourthChainFFirstGroup : NormedAddCommGroup (F →L[ℝ] G) := inferInstance
local instance fourthChainFFirstSpace : NormedSpace ℝ (F →L[ℝ] G) := inferInstance
local instance fourthChainFSecondGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] G) := inferInstance
local instance fourthChainFSecondSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] G) := inferInstance
local instance fourthChainFThirdGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] F →L[ℝ] G) := inferInstance
local instance fourthChainFThirdSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] F →L[ℝ] G) := inferInstance
local instance fourthChainGFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance fourthChainGFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance fourthChainGSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance fourthChainGSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance fourthChainGThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance fourthChainGThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance fourthChainCFirstGroup : NormedAddCommGroup (E →L[ℝ] G) := inferInstance
local instance fourthChainCFirstSpace : NormedSpace ℝ (E →L[ℝ] G) := inferInstance
local instance fourthChainCSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] G) := inferInstance
local instance fourthChainCSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] G) := inferInstance
local instance fourthChainCThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] G) := inferInstance
local instance fourthChainCThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] G) := inferInstance

/-- The fifteen terms in the fourth-order chain rule. -/
def fourthChainValue
    (f1 : F →L[ℝ] G)
    (f2 : F →L[ℝ] F →L[ℝ] G)
    (f3 : F →L[ℝ] F →L[ℝ] F →L[ℝ] G)
    (f4 : F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] G)
    (g1 : E →L[ℝ] F)
    (g2 : E →L[ℝ] E →L[ℝ] F)
    (g3 : E →L[ℝ] E →L[ℝ] E →L[ℝ] F)
    (g4 : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F)
    (q v w z : E) : G :=
      f4 (g1 q) (g1 v) (g1 w) (g1 z) +
      f3 (g2 q v) (g1 w) (g1 z) +
      f3 (g1 v) (g2 q w) (g1 z) +
      f3 (g1 v) (g1 w) (g2 q z) +
      f3 (g1 q) (g2 v w) (g1 z) +
      f2 (g3 q v w) (g1 z) +
      f2 (g2 v w) (g2 q z) +
      f3 (g1 q) (g1 w) (g2 v z) +
      f2 (g2 q w) (g2 v z) +
      f2 (g1 w) (g3 q v z) +
      f3 (g1 q) (g1 v) (g2 w z) +
      f2 (g2 q v) (g2 w z) +
      f2 (g1 v) (g3 q w z) +
      f2 (g1 q) (g3 v w z) +
      f1 (g4 q v w z)

def thirdChainFunction (f : F → G) (g : E → F) (v w z : E) (y : E) : G :=
        fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g y)
          (fderiv ℝ g y v) (fderiv ℝ g y w) (fderiv ℝ g y z) +
        fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ (fderiv ℝ g) y v w) (fderiv ℝ g y z) +
        fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ g y w) (fderiv ℝ (fderiv ℝ g) y v z) +
        fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ g y v) (fderiv ℝ (fderiv ℝ g) y w z) +
        fderiv ℝ f (g y) (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) y v w z)

private def thirdChainTerm1 (f : F → G) (g : E → F) (v w z : E) (y : E) : G :=
  fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g y) (fderiv ℝ g y v) (fderiv ℝ g y w) (fderiv ℝ g y z)

private theorem thirdChainTerm1_derivative {g : E → F} {f : F → G} {x : E}
    (hf : ContDiffAt ℝ 4 f (g x)) (hg : ContDiffAt ℝ 4 g x) (v w z : E) :
    DifferentiableAt ℝ (thirdChainTerm1 f g v w z) x ∧ ∀ q,
      fderiv ℝ (thirdChainTerm1 f g v w z) x q =
        (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) (g x)) ((fderiv ℝ g x) q) ((fderiv ℝ g x) v) ((fderiv ℝ g x) w) ((fderiv ℝ g x) z) +
        (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g x)) ((fderiv ℝ (fderiv ℝ g) x) q v) ((fderiv ℝ g x) w) ((fderiv ℝ g x) z) +
        (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g x)) ((fderiv ℝ g x) v) ((fderiv ℝ (fderiv ℝ g) x) q w) ((fderiv ℝ g x) z) +
        (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g x)) ((fderiv ℝ g x) v) ((fderiv ℝ g x) w) ((fderiv ℝ (fderiv ℝ g) x) q z) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hf₁ : ContDiffAt ℝ 3 (fderiv ℝ f) (g x) := hf.fderiv_right (by norm_num)
  have hf₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ f)) (g x) := hf₁.fderiv_right (by norm_num)
  have hf₃ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) (g x) :=
    hf₂.fderiv_right (by norm_num)
  have hg₁ : ContDiffAt ℝ 3 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have hg₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ g)) x := hg₁.fderiv_right (by norm_num)
  have hg₃ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) x :=
    hg₂.fderiv_right (by norm_num)
  have hF₁ := (hf₁.differentiableAt (by norm_num)).hasFDerivAt.comp x hgd
  have hF₂ := (hf₂.differentiableAt (by norm_num)).hasFDerivAt.comp x hgd
  have hF₃ := (hf₃.differentiableAt one_ne_zero).hasFDerivAt.comp x hgd
  have hG₁ (a : E) := (hg₁.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)
  have hG₂ (a b : E) := ((hg₂.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)
  have hG₃ (a b c : E) := (((hg₃.differentiableAt one_ne_zero).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)).clm_apply (hasFDerivAt_const c x)
  have hright := ((hF₃.clm_apply (hG₁ v)).clm_apply (hG₁ w)).clm_apply (hG₁ z)
  refine ⟨hright.differentiableAt, ?_⟩
  intro q
  change fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g y) (fderiv ℝ g y v) (fderiv ℝ g y w) (fderiv ℝ g y z)) x q = _
  have hval := congrArg (fun L => L q) hright.fderiv
  simpa only [thirdChainTerm1, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, add_apply, zero_apply, map_zero, zero_add, add_zero,
    add_assoc, add_left_comm, add_comm] using hval

private def thirdChainTerm2 (f : F → G) (g : E → F) (v w z : E) (y : E) : G :=
  fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ (fderiv ℝ g) y v w) (fderiv ℝ g y z)

private theorem thirdChainTerm2_derivative {g : E → F} {f : F → G} {x : E}
    (hf : ContDiffAt ℝ 4 f (g x)) (hg : ContDiffAt ℝ 4 g x) (v w z : E) :
    DifferentiableAt ℝ (thirdChainTerm2 f g v w z) x ∧ ∀ q,
      fderiv ℝ (thirdChainTerm2 f g v w z) x q =
        (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g x)) ((fderiv ℝ g x) q) ((fderiv ℝ (fderiv ℝ g) x) v w) ((fderiv ℝ g x) z) +
        (fderiv ℝ (fderiv ℝ f) (g x)) ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x) q v w) ((fderiv ℝ g x) z) +
        (fderiv ℝ (fderiv ℝ f) (g x)) ((fderiv ℝ (fderiv ℝ g) x) v w) ((fderiv ℝ (fderiv ℝ g) x) q z) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hf₁ : ContDiffAt ℝ 3 (fderiv ℝ f) (g x) := hf.fderiv_right (by norm_num)
  have hf₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ f)) (g x) := hf₁.fderiv_right (by norm_num)
  have hf₃ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) (g x) :=
    hf₂.fderiv_right (by norm_num)
  have hg₁ : ContDiffAt ℝ 3 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have hg₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ g)) x := hg₁.fderiv_right (by norm_num)
  have hg₃ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) x :=
    hg₂.fderiv_right (by norm_num)
  have hF₁ := (hf₁.differentiableAt (by norm_num)).hasFDerivAt.comp x hgd
  have hF₂ := (hf₂.differentiableAt (by norm_num)).hasFDerivAt.comp x hgd
  have hF₃ := (hf₃.differentiableAt one_ne_zero).hasFDerivAt.comp x hgd
  have hG₁ (a : E) := (hg₁.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)
  have hG₂ (a b : E) := ((hg₂.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)
  have hG₃ (a b c : E) := (((hg₃.differentiableAt one_ne_zero).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)).clm_apply (hasFDerivAt_const c x)
  have hright := (hF₂.clm_apply (hG₂ v w)).clm_apply (hG₁ z)
  refine ⟨hright.differentiableAt, ?_⟩
  intro q
  change fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ (fderiv ℝ g) y v w) (fderiv ℝ g y z)) x q = _
  have hval := congrArg (fun L => L q) hright.fderiv
  simpa only [thirdChainTerm2, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, add_apply, zero_apply, map_zero, zero_add, add_zero,
    add_assoc, add_left_comm, add_comm] using hval

private def thirdChainTerm3 (f : F → G) (g : E → F) (v w z : E) (y : E) : G :=
  fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ g y w) (fderiv ℝ (fderiv ℝ g) y v z)

private theorem thirdChainTerm3_derivative {g : E → F} {f : F → G} {x : E}
    (hf : ContDiffAt ℝ 4 f (g x)) (hg : ContDiffAt ℝ 4 g x) (v w z : E) :
    DifferentiableAt ℝ (thirdChainTerm3 f g v w z) x ∧ ∀ q,
      fderiv ℝ (thirdChainTerm3 f g v w z) x q =
        (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g x)) ((fderiv ℝ g x) q) ((fderiv ℝ g x) w) ((fderiv ℝ (fderiv ℝ g) x) v z) +
        (fderiv ℝ (fderiv ℝ f) (g x)) ((fderiv ℝ (fderiv ℝ g) x) q w) ((fderiv ℝ (fderiv ℝ g) x) v z) +
        (fderiv ℝ (fderiv ℝ f) (g x)) ((fderiv ℝ g x) w) ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x) q v z) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hf₁ : ContDiffAt ℝ 3 (fderiv ℝ f) (g x) := hf.fderiv_right (by norm_num)
  have hf₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ f)) (g x) := hf₁.fderiv_right (by norm_num)
  have hf₃ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) (g x) :=
    hf₂.fderiv_right (by norm_num)
  have hg₁ : ContDiffAt ℝ 3 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have hg₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ g)) x := hg₁.fderiv_right (by norm_num)
  have hg₃ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) x :=
    hg₂.fderiv_right (by norm_num)
  have hF₁ := (hf₁.differentiableAt (by norm_num)).hasFDerivAt.comp x hgd
  have hF₂ := (hf₂.differentiableAt (by norm_num)).hasFDerivAt.comp x hgd
  have hF₃ := (hf₃.differentiableAt one_ne_zero).hasFDerivAt.comp x hgd
  have hG₁ (a : E) := (hg₁.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)
  have hG₂ (a b : E) := ((hg₂.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)
  have hG₃ (a b c : E) := (((hg₃.differentiableAt one_ne_zero).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)).clm_apply (hasFDerivAt_const c x)
  have hright := (hF₂.clm_apply (hG₁ w)).clm_apply (hG₂ v z)
  refine ⟨hright.differentiableAt, ?_⟩
  intro q
  change fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ g y w) (fderiv ℝ (fderiv ℝ g) y v z)) x q = _
  have hval := congrArg (fun L => L q) hright.fderiv
  simpa only [thirdChainTerm3, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, add_apply, zero_apply, map_zero, zero_add, add_zero,
    add_assoc, add_left_comm, add_comm] using hval

private def thirdChainTerm4 (f : F → G) (g : E → F) (v w z : E) (y : E) : G :=
  fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ g y v) (fderiv ℝ (fderiv ℝ g) y w z)

private theorem thirdChainTerm4_derivative {g : E → F} {f : F → G} {x : E}
    (hf : ContDiffAt ℝ 4 f (g x)) (hg : ContDiffAt ℝ 4 g x) (v w z : E) :
    DifferentiableAt ℝ (thirdChainTerm4 f g v w z) x ∧ ∀ q,
      fderiv ℝ (thirdChainTerm4 f g v w z) x q =
        (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g x)) ((fderiv ℝ g x) q) ((fderiv ℝ g x) v) ((fderiv ℝ (fderiv ℝ g) x) w z) +
        (fderiv ℝ (fderiv ℝ f) (g x)) ((fderiv ℝ (fderiv ℝ g) x) q v) ((fderiv ℝ (fderiv ℝ g) x) w z) +
        (fderiv ℝ (fderiv ℝ f) (g x)) ((fderiv ℝ g x) v) ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x) q w z) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hf₁ : ContDiffAt ℝ 3 (fderiv ℝ f) (g x) := hf.fderiv_right (by norm_num)
  have hf₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ f)) (g x) := hf₁.fderiv_right (by norm_num)
  have hf₃ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) (g x) :=
    hf₂.fderiv_right (by norm_num)
  have hg₁ : ContDiffAt ℝ 3 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have hg₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ g)) x := hg₁.fderiv_right (by norm_num)
  have hg₃ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) x :=
    hg₂.fderiv_right (by norm_num)
  have hF₁ := (hf₁.differentiableAt (by norm_num)).hasFDerivAt.comp x hgd
  have hF₂ := (hf₂.differentiableAt (by norm_num)).hasFDerivAt.comp x hgd
  have hF₃ := (hf₃.differentiableAt one_ne_zero).hasFDerivAt.comp x hgd
  have hG₁ (a : E) := (hg₁.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)
  have hG₂ (a b : E) := ((hg₂.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)
  have hG₃ (a b c : E) := (((hg₃.differentiableAt one_ne_zero).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)).clm_apply (hasFDerivAt_const c x)
  have hright := (hF₂.clm_apply (hG₁ v)).clm_apply (hG₂ w z)
  refine ⟨hright.differentiableAt, ?_⟩
  intro q
  change fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ g y v) (fderiv ℝ (fderiv ℝ g) y w z)) x q = _
  have hval := congrArg (fun L => L q) hright.fderiv
  simpa only [thirdChainTerm4, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, add_apply, zero_apply, map_zero, zero_add, add_zero,
    add_assoc, add_left_comm, add_comm] using hval

private def thirdChainTerm5 (f : F → G) (g : E → F) (v w z : E) (y : E) : G :=
  fderiv ℝ f (g y) (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) y v w z)

private theorem thirdChainTerm5_derivative {g : E → F} {f : F → G} {x : E}
    (hf : ContDiffAt ℝ 4 f (g x)) (hg : ContDiffAt ℝ 4 g x) (v w z : E) :
    DifferentiableAt ℝ (thirdChainTerm5 f g v w z) x ∧ ∀ q,
      fderiv ℝ (thirdChainTerm5 f g v w z) x q =
        (fderiv ℝ (fderiv ℝ f) (g x)) ((fderiv ℝ g x) q) ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x) v w z) +
        (fderiv ℝ f (g x)) ((fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) x) q v w z) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hf₁ : ContDiffAt ℝ 3 (fderiv ℝ f) (g x) := hf.fderiv_right (by norm_num)
  have hf₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ f)) (g x) := hf₁.fderiv_right (by norm_num)
  have hf₃ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) (g x) :=
    hf₂.fderiv_right (by norm_num)
  have hg₁ : ContDiffAt ℝ 3 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have hg₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ g)) x := hg₁.fderiv_right (by norm_num)
  have hg₃ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) x :=
    hg₂.fderiv_right (by norm_num)
  have hF₁ := (hf₁.differentiableAt (by norm_num)).hasFDerivAt.comp x hgd
  have hF₂ := (hf₂.differentiableAt (by norm_num)).hasFDerivAt.comp x hgd
  have hF₃ := (hf₃.differentiableAt one_ne_zero).hasFDerivAt.comp x hgd
  have hG₁ (a : E) := (hg₁.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)
  have hG₂ (a b : E) := ((hg₂.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)
  have hG₃ (a b c : E) := (((hg₃.differentiableAt one_ne_zero).hasFDerivAt.clm_apply
    (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)).clm_apply (hasFDerivAt_const c x)
  have hright := hF₁.clm_apply (hG₃ v w z)
  refine ⟨hright.differentiableAt, ?_⟩
  intro q
  change fderiv ℝ (fun y => fderiv ℝ f (g y) (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) y v w z)) x q = _
  have hval := congrArg (fun L => L q) hright.fderiv
  simpa only [thirdChainTerm5, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, add_apply, zero_apply, map_zero, zero_add, add_zero,
    add_assoc, add_left_comm, add_comm] using hval

theorem fderiv_thirdChainFunction {g : E → F} {f : F → G} {x : E}
    (hf : ContDiffAt ℝ 4 f (g x)) (hg : ContDiffAt ℝ 4 g x) (q v w z : E) :
    fderiv ℝ (thirdChainFunction f g v w z) x q = fourthChainValue
      (fderiv ℝ f (g x)) (fderiv ℝ (fderiv ℝ f) (g x)) (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g x)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) (g x))
      (fderiv ℝ g x) (fderiv ℝ (fderiv ℝ g) x) (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) x) q v w z := by
  obtain ⟨h1, d1⟩ := thirdChainTerm1_derivative hf hg v w z
  obtain ⟨h2, d2⟩ := thirdChainTerm2_derivative hf hg v w z
  obtain ⟨h3, d3⟩ := thirdChainTerm3_derivative hf hg v w z
  obtain ⟨h4, d4⟩ := thirdChainTerm4_derivative hf hg v w z
  obtain ⟨h5, d5⟩ := thirdChainTerm5_derivative hf hg v w z
  change fderiv ℝ (thirdChainTerm1 f g v w z + thirdChainTerm2 f g v w z +
    thirdChainTerm3 f g v w z + thirdChainTerm4 f g v w z + thirdChainTerm5 f g v w z) x q = _
  rw [fderiv_add (((h1.add h2).add h3).add h4) h5, fderiv_add ((h1.add h2).add h3) h4,
    fderiv_add (h1.add h2) h3, fderiv_add h1 h2]
  simp only [add_apply, d1, d2, d3, d4, d5, fourthChainValue]
  abel

/-- The fourth-order chain rule requires only C⁴ regularity of both maps. -/
theorem fourth_fderiv_comp {g : E → F} {f : F → G} {x : E}
    (hf : ContDiffAt ℝ 4 f (g x)) (hg : ContDiffAt ℝ 4 g x) (q v w z : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => f (g y))))) x q v w z = fourthChainValue
      (fderiv ℝ f (g x)) (fderiv ℝ (fderiv ℝ f) (g x)) (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g x)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) (g x))
      (fderiv ℝ g x) (fderiv ℝ (fderiv ℝ g) x) (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) x) q v w z := by
  have hc₁ : ContDiffAt ℝ 3 (fderiv ℝ (fun y => f (g y))) x :=
    (hf.comp x hg).fderiv_right (by norm_num)
  have hc₂ : ContDiffAt ℝ 2 (fderiv ℝ (fderiv ℝ (fun y => f (g y)))) x :=
    hc₁.fderiv_right (by norm_num)
  have hc₃ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => f (g y))))) x :=
    hc₂.fderiv_right (by norm_num)
  have hleft := (((hc₃.differentiableAt one_ne_zero).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x)).clm_apply (hasFDerivAt_const z x)
  have heq : (fun y => fderiv ℝ (fderiv ℝ (fderiv ℝ (fun a => f (g a)))) y v w z) =ᶠ[𝓝 x]
      (fun y =>
        fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g y)
          (fderiv ℝ g y v) (fderiv ℝ g y w) (fderiv ℝ g y z) +
        fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ (fderiv ℝ g) y v w) (fderiv ℝ g y z) +
        fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ g y w) (fderiv ℝ (fderiv ℝ g) y v z) +
        fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ g y v) (fderiv ℝ (fderiv ℝ g) y w z) +
        fderiv ℝ f (g y) (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) y v w z)) := by
    filter_upwards [hg.eventually (by norm_num),
      hg.continuousAt.tendsto.eventually (hf.eventually (by norm_num))] with y hgy hfy
    exact third_fderiv_comp (hfy.of_le (by norm_num)) (hgy.of_le (by norm_num)) v w z
  have hleftval := congrArg (fun L => L q) hleft.fderiv
  have hleftid : fderiv ℝ
      (fun y => fderiv ℝ (fderiv ℝ (fderiv ℝ (fun a => f (g a)))) y v w z) x q =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => f (g y))))) x q v w z := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      add_apply, zero_apply, map_zero, zero_add, add_zero] using hleftval
  rw [← hleftid]
  exact (congrArg (fun L : E →L[ℝ] G => L q) (heq.fderiv_eq (𝕜 := ℝ))).trans
    (fderiv_thirdChainFunction hf hg q v w z)

end OAI.Analysis.PDE.Elliptic
