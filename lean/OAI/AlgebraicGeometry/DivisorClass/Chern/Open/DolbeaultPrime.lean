import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultZeroKernelMap

/-! # Dolbeault Prime -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultPrime

noncomputable section

section

/-! Pure open-domain forms, with the original full scalar-character condition. -/

open _root_.TopologicalSpace
open scoped _root_.Topology ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {U V : Opens E} {n p q : ℕ}

omit [IsScalarTower ℝ ℂ E] in
/-- The character condition without a degree cast, for intermediate derivatives. -/
def OpenFormHasBidegree (p q : ℕ) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) : Prop :=
  ∀ (x : U) (z : ℂˣ) (v : Fin n → E),
    form x (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * form x v

omit [IsScalarTower ℝ ℂ E] in
theorem openFormHasBidegree_iff (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (p + q)) :
    OpenFormHasBidegree p q form ↔ ∀ x : U, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (form x) := Iff.rfl

omit [IsScalarTower ℝ ℂ E] in
def pureOpenFormSubmodule (U : Opens E) (p q : ℕ) :
    Submodule ℂ (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (p + q)) where
  carrier := OpenFormHasBidegree p q
  zero_mem' := fun _ => (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E p q).zero_mem
  add_mem' := fun hf hg x => (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E p q).add_mem (hf x) (hg x)
  smul_mem' := fun c _ hf x => (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E p q).smul_mem c (hf x)

omit [IsScalarTower ℝ ℂ E] in
abbrev PureOpenForm (U : Opens E) (p q : ℕ) := ↥(pureOpenFormSubmodule U p q)

omit [IsScalarTower ℝ ℂ E] in
theorem openFormHasBidegree_restrict (h : V ≤ U) {form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n}
    (hf : OpenFormHasBidegree p q form) :
    OpenFormHasBidegree p q (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h form) :=
  fun x => hf ⟨x, h x.property⟩

omit [IsScalarTower ℝ ℂ E] in
def pureOpenFormRestrict (h : V ≤ U) : PureOpenForm U p q →ₗ[ℂ] PureOpenForm V p q where
  toFun form := ⟨Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h form.1, openFormHasBidegree_restrict h form.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsScalarTower ℝ ℂ E] in
theorem openFormHasBidegree_extension {form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (p + q)}
    (hf : OpenFormHasBidegree p q form) (x : U) :
    ∀ᶠ y in 𝓝 (x : E), Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (form.extension y) := by
  filter_upwards [U.isOpen.mem_nhds x.property] with y hy
  rw [show form.extension y = form ⟨y, hy⟩ from form.extension_apply ⟨y, hy⟩]
  exact hf ⟨y, hy⟩

theorem openDolbeaultD_hasBidegree {form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n} (hn : n = p + q)
    (hf : OpenFormHasBidegree p q form) : OpenFormHasBidegree p (q + 1) (DolbeaultOpen.openDolbeaultD n form) := by
  subst n
  intro x z v
  exact Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime_bidegree_character
    ((form.smooth.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp))
    (openFormHasBidegree_extension hf x) z v

omit [IsScalarTower ℝ ℂ E] in
/-- Smooth `(0,q)` forms, with the total degree written as `q`. -/
def antiOpenFormSubmodule (U : Opens E) (q : ℕ) : Submodule ℂ (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U q) where
  carrier := OpenFormHasBidegree 0 q
  zero_mem' := by intro x z v; simp
  add_mem' := by
    intro f g hf hg x z v
    change f x (fun i => (z : ℂ) • v i) + g x (fun i => (z : ℂ) • v i) =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 q z * (f x v + g x v)
    rw [hf x z v, hg x z v, mul_add]
  smul_mem' := by
    intro c f hf x z v
    change c * f x (fun i => (z : ℂ) • v i) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 q z * (c * f x v)
    rw [hf x z v]
    ring

omit [IsScalarTower ℝ ℂ E] in
abbrev AntiOpenForm (U : Opens E) (q : ℕ) := ↥(antiOpenFormSubmodule U q)

omit [IsScalarTower ℝ ℂ E] in
instance antiOpenFormAddCommGroup (U : Opens E) (q : ℕ) : AddCommGroup (AntiOpenForm U q) :=
  Module.addCommMonoidToAddCommGroup ℂ

omit [IsScalarTower ℝ ℂ E] in
def antiOpenFormRestrict (h : V ≤ U) : AntiOpenForm U q →ₗ[ℂ] AntiOpenForm V q where
  toFun form := ⟨Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h form.1, openFormHasBidegree_restrict h form.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original antiholomorphic differential restricted to actual `(0,q)` forms. -/
def pureOpenDolbeaultD (U : Opens E) (q : ℕ) :
    AntiOpenForm U q →ₗ[ℂ] AntiOpenForm U (q + 1) where
  toFun form := ⟨DolbeaultOpen.openDolbeaultD q form.1, openDolbeaultD_hasBidegree (by omega) form.2⟩
  map_add' f g := Subtype.ext ((DolbeaultOpen.openDolbeaultD q).map_add f.1 g.1)
  map_smul' c f := Subtype.ext ((DolbeaultOpen.openDolbeaultD q).map_smul c f.1)

theorem pureOpenDolbeaultD_restrict (h : V ≤ U) (form : AntiOpenForm U q) :
    antiOpenFormRestrict h (pureOpenDolbeaultD U q form) =
      pureOpenDolbeaultD V q (antiOpenFormRestrict h form) :=
  Subtype.ext (DolbeaultZeroKernelMap.openDolbeaultD_restrict h form.1)

end

/-! The complementary holomorphic differential and its actual bidegree. -/

open _root_.TopologicalSpace
open scoped _root_.Topology ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {U : Opens E} {n p q : ℕ}

def openDolbeaultPrime (U : Opens E) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1) where
  toFun form := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form - DolbeaultOpen.openDolbeaultD n form
  map_add' f g := by
    change Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d (f + g) - DolbeaultOpen.openDolbeaultD n (f + g) =
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d f - DolbeaultOpen.openDolbeaultD n f) +
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d g - DolbeaultOpen.openDolbeaultD n g)
    rw [map_add, map_add]
    abel
  map_smul' c f := by
    change Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d (c • f) - DolbeaultOpen.openDolbeaultD n (c • f) =
      c • (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d f - DolbeaultOpen.openDolbeaultD n f)
    rw [map_smul, map_smul]
    exact (smul_sub c (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d f) (DolbeaultOpen.openDolbeaultD n f)).symm

theorem openDolbeaultPrime_apply (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) (x : U) :
    openDolbeaultPrime U n form x = Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime form.extension x := by
  change extDeriv form.extension x - Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime form.extension x = _
  rw [← Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime_add_extDerivDoublePrime, add_sub_cancel_right]

theorem openDolbeaultPrime_add_D (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) :
    openDolbeaultPrime U n form + DolbeaultOpen.openDolbeaultD n form = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form := by
  change (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form - DolbeaultOpen.openDolbeaultD n form) + DolbeaultOpen.openDolbeaultD n form = _
  exact sub_add_cancel (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form) (DolbeaultOpen.openDolbeaultD n form)

theorem openDolbeaultPrime_hasBidegree {form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n} (hn : n = p + q)
    (hf : OpenFormHasBidegree p q form) :
    OpenFormHasBidegree (p + 1) q (openDolbeaultPrime U n form) := by
  subst n
  intro x z v
  rw [openDolbeaultPrime_apply]
  exact Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime_bidegree_character
    ((form.smooth.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp))
    (openFormHasBidegree_extension hf x) z v

theorem openDolbeault_second_sum (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) :
    openDolbeaultPrime U (n + 1) (openDolbeaultPrime U n form) +
      (DolbeaultOpen.openDolbeaultD (n + 1) (openDolbeaultPrime U n form) +
        openDolbeaultPrime U (n + 1) (DolbeaultOpen.openDolbeaultD n form)) +
      DolbeaultOpen.openDolbeaultD (n + 1) (DolbeaultOpen.openDolbeaultD n form) = 0 := by
  have hsum := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_squared form
  rw [← openDolbeaultPrime_add_D form, map_add,
    ← openDolbeaultPrime_add_D (openDolbeaultPrime U n form),
    ← openDolbeaultPrime_add_D (DolbeaultOpen.openDolbeaultD n form)] at hsum
  convert hsum using 1
  abel

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultPrime
