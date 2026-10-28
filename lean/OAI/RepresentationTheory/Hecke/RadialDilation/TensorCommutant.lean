import OAI.RepresentationTheory.Hecke.RadialDilation.TestSections

/-! # Tensor Commutant -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization

noncomputable section

section

/-! Extension of actual local operators by acting on product sections. -/

open scoped Classical _root_.Topology
open Filter

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

omit [T2Space X] [T2Space Y] in
theorem uncurry_test_locallyConstant
    (s : Y → TestSections.Realization.lcCompactSpace X) (hs : IsLocallyConstant s) :
    IsLocallyConstant (fun p : X × Y => (s p.2).val p.1) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  have h₁ := (hs.comp_continuous (continuous_snd : Continuous (Prod.snd : X × Y → Y))).eventually_eq p
  have h₂ := ((s p.2).property.1.comp_continuous
    (continuous_fst : Continuous (Prod.fst : X × Y → X))).eventually_eq p
  filter_upwards [h₁, h₂] with p' hp₁ hp₂
  change s p'.2 = s p.2 at hp₁
  rw [hp₁]
  exact hp₂

theorem uncurry_test_compactSupport
    (s : Y → TestSections.Realization.lcCompactSpace X) (hs : IsLocallyConstant s) (hc : HasCompactSupport s) :
    HasCompactSupport (fun p : X × Y => (s p.2).val p.1) := by
  let K : Set X := ⋃ f ∈ Set.range s, tsupport f.val
  have hK : IsCompact K :=
    (TestSections.Realization.locallyConstant_compact_range_finite s hs hc).isCompact_biUnion (fun f _ => f.property.2)
  apply HasCompactSupport.intro (hK.prod hc)
  rintro ⟨x, y⟩ hxy
  by_contra hn
  have hy : s y ≠ 0 := by
    intro hy
    rw [hy] at hn
    exact hn rfl
  have hx : x ∈ K := Set.mem_iUnion.mpr ⟨s y,
    Set.mem_iUnion.mpr ⟨⟨y, rfl⟩, subset_tsupport (s y).val hn⟩⟩
  exact hxy ⟨hx, subset_tsupport s hy⟩

def uncurryTest (s : Y → TestSections.Realization.lcCompactSpace X) (hs : IsLocallyConstant s) (hc : HasCompactSupport s) :
    TestSections.Realization.lcCompactSpace (X × Y) :=
  ⟨fun p => (s p.2).val p.1, uncurry_test_locallyConstant s hs, uncurry_test_compactSupport s hs hc⟩

/-- The operator acts on every actual section at a fixed auxiliary point.
Preservation of the test space is proved from compactness and local constancy. -/
def extendTestLinear (T : TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X) :
    TestSections.Realization.lcCompactSpace (X × Y) →ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y) where
  toFun f := uncurryTest (fun y => T (TestSections.Realization.testSection y f))
    ((TestSections.Realization.testSection_locallyConstant f).comp T)
    ((TestSections.Realization.testSection_compactSupport f).comp_left T.map_zero)
  map_add' f g := by
    apply Subtype.ext
    funext p
    change (T (TestSections.Realization.testSection p.2 (f + g))).val p.1 = _
    rw [map_add, map_add]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext p
    change (T (TestSections.Realization.testSection p.2 (c • f))).val p.1 = _
    rw [map_smul, map_smul]
    rfl

theorem testSection_extend (T : TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (f : TestSections.Realization.lcCompactSpace (X × Y)) (y : Y) :
    TestSections.Realization.testSection y (extendTestLinear T f) = T (TestSections.Realization.testSection y f) := by
  apply Subtype.ext
  rfl

def extendTestEquiv (T : TestSections.Realization.lcCompactSpace X ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace X) :
    TestSections.Realization.lcCompactSpace (X × Y) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y) :=
  { extendTestLinear T.toLinearMap with
    invFun := extendTestLinear T.symm.toLinearMap
    left_inv := by
      intro f
      apply Subtype.ext
      funext p
      change (T.symm (TestSections.Realization.testSection p.2 (extendTestLinear T.toLinearMap f))).val p.1 = f.val p
      rw [testSection_extend]
      change (T.symm (T (TestSections.Realization.testSection p.2 f))).val p.1 = f.val p
      rw [T.symm_apply_apply]
      rfl
    right_inv := by
      intro f
      apply Subtype.ext
      funext p
      change (T (TestSections.Realization.testSection p.2 (extendTestLinear T.symm.toLinearMap f))).val p.1 = f.val p
      rw [testSection_extend]
      change (T (T.symm (TestSections.Realization.testSection p.2 f))).val p.1 = f.val p
      rw [T.apply_symm_apply]
      rfl }

def extendTestHom : (TestSections.Realization.lcCompactSpace X ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace X) →*
    (TestSections.Realization.lcCompactSpace (X × Y) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y)) where
  toFun := extendTestEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    rfl
  map_mul' T U := by
    apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    funext p
    change (T (U (TestSections.Realization.testSection p.2 f))).val p.1 =
      (T (TestSections.Realization.testSection p.2 (extendTestLinear U.toLinearMap f))).val p.1
    rw [testSection_extend]
    rfl

end

section

/-! Pure test tensors and changes of position coordinates. -/

open scoped Classical

def testPullback {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace X where
  toFun f := ⟨f.val ∘ e, f.property.1.comp_continuous e.continuous, f.property.2.comp_homeomorph e⟩
  invFun f := ⟨f.val ∘ e.symm, f.property.1.comp_continuous e.symm.continuous,
    f.property.2.comp_homeomorph e.symm⟩
  left_inv f := by apply Subtype.ext; funext x; simp
  right_inv f := by apply Subtype.ext; funext x; simp
  map_add' f g := rfl
  map_smul' c f := rfl

def conjugateLinearAut {S T : Type*} [AddCommGroup S] [AddCommGroup T] [Module ℂ S] [Module ℂ T]
    (e : S ≃ₗ[ℂ] T) : (S ≃ₗ[ℂ] S) →* (T ≃ₗ[ℂ] T) where
  toFun U := e.symm.trans (U.trans e)
  map_one' := by apply LinearEquiv.ext; intro f; simp
  map_mul' U V := by apply LinearEquiv.ext; intro f; simp

theorem conjugateLinearAut_neg {S T : Type*} [AddCommGroup S] [AddCommGroup T]
    [Module ℂ S] [Module ℂ T] (e : S ≃ₗ[ℂ] T) :
    conjugateLinearAut e (LinearEquiv.neg ℂ) = LinearEquiv.neg ℂ := by
  apply LinearEquiv.ext
  intro f
  change e (-e.symm f) = -f
  rw [map_neg, e.apply_symm_apply]

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

def tensorTest (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) : TestSections.Realization.lcCompactSpace (X × Y) := by
  refine uncurryTest (fun y => g.val y • f) (g.property.1.comp (fun c : ℂ => c • f)) ?_
  apply HasCompactSupport.intro g.property.2
  intro y hy
  have hz : g.val y = 0 := image_eq_zero_of_notMem_tsupport hy
  rw [hz, zero_smul]

theorem tensorTest_apply (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) (x : X) (y : Y) :
    (tensorTest f g).val (x, y) = f.val x * g.val y := mul_comm _ _

theorem testSection_tensor (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) (y : Y) :
    TestSections.Realization.testSection y (tensorTest f g) = g.val y • f := by
  apply Subtype.ext
  rfl

theorem extendTestLinear_tensor (T : TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) :
    extendTestLinear T (tensorTest f g) = tensorTest (T f) g := by
  apply Subtype.ext
  funext p
  change (T (TestSections.Realization.testSection p.2 (tensorTest f g))).val p.1 = (tensorTest (T f) g).val p
  rw [testSection_tensor, map_smul]
  rfl

theorem extendTestHom_tensor (T : TestSections.Realization.lcCompactSpace X ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) :
    extendTestHom T (tensorTest f g) = tensorTest (T f) g :=
  extendTestLinear_tensor T.toLinearMap f g

theorem extendTestHom_neg :
    (extendTestHom (X := X) (Y := Y)) (LinearEquiv.neg ℂ) = LinearEquiv.neg ℂ := by
  apply LinearEquiv.ext
  intro f
  apply Subtype.ext
  rfl

end

section

/-! Finite pure-tensor expansions of actual product test functions. -/

open scoped Classical

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

def testFiberCoefficient (s : Y → TestSections.Realization.lcCompactSpace X) (hs : IsLocallyConstant s)
    (hc : HasCompactSupport s) (v : TestSections.Realization.lcCompactSpace X) : TestSections.Realization.lcCompactSpace Y := by
  by_cases hv : v = 0
  · exact 0
  · let K : Set Y := {y | s y = v}
    have hK : IsClopen K := ⟨hs.isClosed_fiber v, hs.isOpen_fiber v⟩
    have hcompact : IsCompact K := hc.of_isClosed_subset hK.isClosed (by
      intro y hy
      apply subset_tsupport s
      change s y ≠ 0
      rwa [show s y = v from hy])
    refine ⟨K.indicator (fun _ => 1), (LocallyConstant.charFn ℂ hK).isLocallyConstant, ?_⟩
    apply HasCompactSupport.intro hcompact
    intro y hy
    exact Set.indicator_of_notMem hy _

omit [T2Space X] in
theorem testFiberCoefficient_apply (s : Y → TestSections.Realization.lcCompactSpace X) (hs : IsLocallyConstant s)
    (hc : HasCompactSupport s) (v : TestSections.Realization.lcCompactSpace X) (y : Y) :
    (testFiberCoefficient s hs hc v).val y = if s y = v then (if v = 0 then 0 else 1) else 0 := by
  by_cases hv : v = 0
  · simp [testFiberCoefficient, hv]
  · simp [testFiberCoefficient, hv, Set.indicator]

theorem test_tensor_expansion (f : TestSections.Realization.lcCompactSpace (X × Y)) :
    ∃ r : Finset (TestSections.Realization.lcCompactSpace X), ∃ g : TestSections.Realization.lcCompactSpace X → TestSections.Realization.lcCompactSpace Y,
      f = ∑ v ∈ r, tensorTest v (g v) := by
  let s := fun y => TestSections.Realization.testSection y f
  let r := (TestSections.Realization.testSection_range_finite f).toFinset
  let g := testFiberCoefficient s (TestSections.Realization.testSection_locallyConstant f) (TestSections.Realization.testSection_compactSupport f)
  refine ⟨r, g, ?_⟩
  apply Subtype.ext
  funext p
  change f.val (p.1, p.2) = (∑ v ∈ r, tensorTest v (g v)).val (p.1, p.2)
  simp only [Submodule.coe_sum, Finset.sum_apply, tensorTest_apply]
  change f.val (p.1, p.2) = ∑ v ∈ r, v.val p.1 *
    (testFiberCoefficient s (TestSections.Realization.testSection_locallyConstant f) (TestSections.Realization.testSection_compactSupport f) v).val p.2
  simp_rw [testFiberCoefficient_apply]
  rw [Finset.sum_eq_single (s p.2)]
  · simp only [ite_true]
    by_cases hz : s p.2 = 0
    · rw [ite_eq_left hz, mul_zero]
      exact congrArg (fun v : TestSections.Realization.lcCompactSpace X => v.val p.1) hz
    · rw [ite_eq_right hz, mul_one]
      rfl
  · intro v _ hv
    rw [ite_eq_right (Ne.symm hv), mul_zero]
  · intro hs
    exact (hs ((TestSections.Realization.testSection_range_finite f).mem_toFinset.mpr ⟨p.2, rfl⟩)).elim

theorem test_linear_ext {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T U : TestSections.Realization.lcCompactSpace (X × Y) →ₗ[ℂ] V)
    (h : ∀ f : TestSections.Realization.lcCompactSpace X, ∀ g : TestSections.Realization.lcCompactSpace Y, T (tensorTest f g) = U (tensorTest f g)) :
    T = U := by
  apply LinearMap.ext
  intro f
  obtain ⟨r, g, hf⟩ := test_tensor_expansion f
  rw [hf, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun v _ => h v (g v))

end

section

/-! Independent local actions commute on the full product test space. -/

open scoped Classical

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

theorem testPullback_swap_tensor (f : TestSections.Realization.lcCompactSpace Y) (g : TestSections.Realization.lcCompactSpace X) :
    testPullback (Homeomorph.prodComm X Y) (tensorTest f g) = tensorTest g f := by
  apply Subtype.ext
  funext p
  change (tensorTest f g).val (p.2, p.1) = (tensorTest g f).val (p.1, p.2)
  rw [tensorTest_apply, tensorTest_apply, mul_comm]

theorem testPullback_swap_symm_tensor (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) :
    (testPullback (Homeomorph.prodComm X Y)).symm (tensorTest f g) = tensorTest g f := by
  apply (testPullback (Homeomorph.prodComm X Y)).injective
  rw [LinearEquiv.apply_symm_apply, testPullback_swap_tensor]

def rightTestHom : (TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace Y) →*
    (TestSections.Realization.lcCompactSpace (X × Y) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y)) :=
  (conjugateLinearAut (testPullback (Homeomorph.prodComm X Y))).comp extendTestHom

theorem rightTestHom_tensor (U : TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace Y)
    (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) :
    rightTestHom U (tensorTest f g) = tensorTest f (U g) := by
  change testPullback (Homeomorph.prodComm X Y)
    (extendTestHom U ((testPullback (Homeomorph.prodComm X Y)).symm (tensorTest f g))) = _
  rw [testPullback_swap_symm_tensor, extendTestHom_tensor, testPullback_swap_tensor]

theorem left_right_test_commute (U : TestSections.Realization.lcCompactSpace X ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (V : TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace Y) :
    Commute (extendTestHom (Y := Y) U) (rightTestHom (X := X) V) := by
  have h : (extendTestHom U).toLinearMap.comp (rightTestHom V).toLinearMap =
      (rightTestHom V).toLinearMap.comp (extendTestHom U).toLinearMap := by
    apply test_linear_ext
    intro f g
    change extendTestHom U (rightTestHom V (tensorTest f g)) =
      rightTestHom V (extendTestHom U (tensorTest f g))
    rw [rightTestHom_tensor, extendTestHom_tensor, extendTestHom_tensor, rightTestHom_tensor]
  apply LinearEquiv.ext
  intro f
  exact LinearMap.congr_fun h f

def tensorTestAut :
    ((TestSections.Realization.lcCompactSpace X ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace X) × (TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace Y)) →*
      (TestSections.Realization.lcCompactSpace (X × Y) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y)) :=
  extendTestHom.noncommCoprod rightTestHom left_right_test_commute

theorem tensorTestAut_apply (U : TestSections.Realization.lcCompactSpace X ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (V : TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace Y)
    (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) :
    tensorTestAut (U, V) (tensorTest f g) = tensorTest (U f) (V g) := by
  change extendTestHom U (rightTestHom V (tensorTest f g)) = _
  rw [rightTestHom_tensor, extendTestHom_tensor]

theorem tensorTest_smul_pair (c d : ℂ) (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) :
    tensorTest (c • f) (d • g) = (c * d) • tensorTest f g := by
  apply Subtype.ext
  funext p
  change (d * g.val p.2) * (c * f.val p.1) = (c * d) * (g.val p.2 * f.val p.1)
  ring

theorem tensorTestAut_phases (U : TestSections.Realization.lcCompactSpace X ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (V : TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace Y)
    (f f' : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) (c d : ℂ)
    (hU : U f = c • f') (hV : V g = d • g) :
    tensorTestAut (U, V) (tensorTest f g) = (c * d) • tensorTest f' g := by
  rw [tensorTestAut_apply, hU, hV, tensorTest_smul_pair]

end

section

/-! An operator commuting with an irreducible local action acts on the auxiliary factor. -/

open scoped Classical

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

def tensorLeftLinear (f : TestSections.Realization.lcCompactSpace X) :
    TestSections.Realization.lcCompactSpace Y →ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y) where
  toFun g := tensorTest f g
  map_add' g h := by apply Subtype.ext; funext p; exact add_mul _ _ _
  map_smul' c g := by apply Subtype.ext; funext p; exact mul_assoc _ _ _

def tensorRightLinear (g : TestSections.Realization.lcCompactSpace Y) :
    TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y) where
  toFun f := tensorTest f g
  map_add' f h := by apply Subtype.ext; funext p; exact mul_add _ _ _
  map_smul' c f := by apply Subtype.ext; funext p; exact mul_left_comm _ _ _

def testRightSection (x : X) : TestSections.Realization.lcCompactSpace (X × Y) →ₗ[ℂ] TestSections.Realization.lcCompactSpace Y :=
  (TestSections.Realization.testSection x).comp (testPullback (Homeomorph.prodComm Y X)).toLinearMap

theorem testRightSection_tensor (x : X) (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) :
    testRightSection x (tensorTest f g) = f.val x • g := by
  apply Subtype.ext
  funext y
  exact mul_comm _ _

def rightTestLinear (T : TestSections.Realization.lcCompactSpace Y →ₗ[ℂ] TestSections.Realization.lcCompactSpace Y) :
    TestSections.Realization.lcCompactSpace (X × Y) →ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y) :=
  (testPullback (Homeomorph.prodComm X Y)).toLinearMap.comp
    ((extendTestLinear T).comp (testPullback (Homeomorph.prodComm X Y)).symm.toLinearMap)

theorem rightTestLinear_tensor (T : TestSections.Realization.lcCompactSpace Y →ₗ[ℂ] TestSections.Realization.lcCompactSpace Y)
    (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) :
    rightTestLinear T (tensorTest f g) = tensorTest f (T g) := by
  change testPullback (Homeomorph.prodComm X Y)
    (extendTestLinear T ((testPullback (Homeomorph.prodComm X Y)).symm (tensorTest f g))) = _
  rw [testPullback_swap_symm_tensor, extendTestLinear_tensor, testPullback_swap_tensor]

def auxiliaryTraceOperator (U : TestSections.Realization.lcCompactSpace (X × Y) →ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y))
    (f₀ : TestSections.Realization.lcCompactSpace X) (x₀ : X) : TestSections.Realization.lcCompactSpace Y →ₗ[ℂ] TestSections.Realization.lcCompactSpace Y :=
  (testRightSection x₀).comp (U.comp (tensorLeftLinear f₀))

theorem local_commutant_tensor_formula {J : Type*}
    (H : J → TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (hSchur : ∀ A : TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X,
      (∀ i f, A (H i f) = H i (A f)) → ∃ c : ℂ, ∀ f, A f = c • f)
    (U : TestSections.Realization.lcCompactSpace (X × Y) →ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y))
    (hU : ∀ i f, U (extendTestLinear (H i) f) = extendTestLinear (H i) (U f))
    (f₀ : TestSections.Realization.lcCompactSpace X) (x₀ : X) (hf₀ : f₀.val x₀ = 1)
    (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) :
    U (tensorTest f g) = tensorTest f (auxiliaryTraceOperator U f₀ x₀ g) := by
  apply Subtype.ext
  funext p
  let A : TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X :=
    (TestSections.Realization.testSection p.2).comp (U.comp (tensorRightLinear g))
  have hA : ∀ i f, A (H i f) = H i (A f) := by
    intro i f
    change TestSections.Realization.testSection p.2 (U (tensorTest (H i f) g)) =
      H i (TestSections.Realization.testSection p.2 (U (tensorTest f g)))
    rw [← extendTestLinear_tensor, hU, testSection_extend]
  obtain ⟨c, hc⟩ := hSchur A hA
  have hcf := congrArg (fun v : TestSections.Realization.lcCompactSpace X => v.val p.1) (hc f)
  have hc₀ := congrArg (fun v : TestSections.Realization.lcCompactSpace X => v.val x₀) (hc f₀)
  change (U (tensorTest f₀ g)).val (x₀, p.2) = c * f₀.val x₀ at hc₀
  rw [hf₀, mul_one] at hc₀
  change (U (tensorTest f g)).val (p.1, p.2) = c * f.val p.1 at hcf
  change (U (tensorTest f g)).val (p.1, p.2) =
    (U (tensorTest f₀ g)).val (x₀, p.2) * f.val p.1
  rw [hc₀]
  exact hcf

/-- The auxiliary operator is obtained by an actual section and evaluation,
and the factorization holds on all test functions by finite tensor expansion. -/
theorem local_commutant_factors {J : Type*}
    (H : J → TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (hSchur : ∀ A : TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X,
      (∀ i f, A (H i f) = H i (A f)) → ∃ c : ℂ, ∀ f, A f = c • f)
    (U : TestSections.Realization.lcCompactSpace (X × Y) →ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y))
    (hU : ∀ i f, U (extendTestLinear (H i) f) = extendTestLinear (H i) (U f))
    (f₀ : TestSections.Realization.lcCompactSpace X) (x₀ : X) (hf₀ : f₀.val x₀ = 1) :
    U = rightTestLinear (auxiliaryTraceOperator U f₀ x₀) := by
  apply test_linear_ext
  intro f g
  rw [local_commutant_tensor_formula H hSchur U hU f₀ x₀ hf₀, rightTestLinear_tensor]

end

section

/-! An invertible commutant operator induces an invertible auxiliary operator. -/

open scoped Classical

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

theorem tensorLeft_injective (f₀ : TestSections.Realization.lcCompactSpace X) (x₀ : X) (hf₀ : f₀.val x₀ = 1) :
    Function.Injective (tensorTest f₀ (Y := Y)) := by
  intro g h heq
  have hs := congrArg (testRightSection x₀) heq
  simpa only [testRightSection_tensor, hf₀, one_smul] using hs

theorem inverse_commutes_test_action {J : Type*}
    (H : J → TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (U : TestSections.Realization.lcCompactSpace (X × Y) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y))
    (hU : ∀ i f, U (extendTestLinear (H i) f) = extendTestLinear (H i) (U f)) :
    ∀ i f, U.symm (extendTestLinear (H i) f) = extendTestLinear (H i) (U.symm f) := by
  intro i f
  apply U.injective
  rw [U.apply_symm_apply, hU, U.apply_symm_apply]

theorem local_commutant_equiv_factors {J : Type*}
    (H : J → TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (hSchur : ∀ A : TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X,
      (∀ i f, A (H i f) = H i (A f)) → ∃ c : ℂ, ∀ f, A f = c • f)
    (U : TestSections.Realization.lcCompactSpace (X × Y) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y))
    (hU : ∀ i f, U (extendTestLinear (H i) f) = extendTestLinear (H i) (U f))
    (f₀ : TestSections.Realization.lcCompactSpace X) (x₀ : X) (hf₀ : f₀.val x₀ = 1) :
    ∃ V : TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace Y,
      U = rightTestHom V ∧ V.toLinearMap = auxiliaryTraceOperator U.toLinearMap f₀ x₀ := by
  let T := auxiliaryTraceOperator U.toLinearMap f₀ x₀
  let S := auxiliaryTraceOperator U.symm.toLinearMap f₀ x₀
  have hT (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) :
      U (tensorTest f g) = tensorTest f (T g) :=
    local_commutant_tensor_formula H hSchur U.toLinearMap hU f₀ x₀ hf₀ f g
  have hS (f : TestSections.Realization.lcCompactSpace X) (g : TestSections.Realization.lcCompactSpace Y) :
      U.symm (tensorTest f g) = tensorTest f (S g) :=
    local_commutant_tensor_formula H hSchur U.symm.toLinearMap
      (inverse_commutes_test_action H U hU) f₀ x₀ hf₀ f g
  have hST (g : TestSections.Realization.lcCompactSpace Y) : S (T g) = g := by
    apply tensorLeft_injective f₀ x₀ hf₀
    rw [← hS, ← hT, U.symm_apply_apply]
  have hTS (g : TestSections.Realization.lcCompactSpace Y) : T (S g) = g := by
    apply tensorLeft_injective f₀ x₀ hf₀
    rw [← hT, ← hS, U.apply_symm_apply]
  let V : TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace Y :=
    { T with invFun := S, left_inv := hST, right_inv := hTS }
  refine ⟨V, ?_, rfl⟩
  have heq : U.toLinearMap = (rightTestHom V).toLinearMap := by
    apply test_linear_ext
    intro f g
    exact (hT f g).trans (rightTestHom_tensor V f g).symm
  exact LinearEquiv.toLinearMap_injective heq

end

/-! A local intertwiner can be factored out of an actual tensor-space intertwiner. -/

open scoped Classical

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

theorem extendTestHom_intertwines {J : Type*}
    (H : J → TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X) (φ : J → J)
    (L : TestSections.Realization.lcCompactSpace X ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (hL : ∀ i f, L (H i f) = H (φ i) (L f)) (i : J)
    (f : TestSections.Realization.lcCompactSpace (X × Y)) :
    extendTestHom L (extendTestLinear (H i) f) =
      extendTestLinear (H (φ i)) (extendTestHom L f) := by
  have heq : (extendTestHom (Y := Y) L).toLinearMap.comp (extendTestLinear (H i)) =
      (extendTestLinear (H (φ i))).comp (extendTestHom L).toLinearMap := by
    apply test_linear_ext
    intro a b
    change extendTestHom L (extendTestLinear (H i) (tensorTest a b)) =
      extendTestLinear (H (φ i)) (extendTestHom L (tensorTest a b))
    rw [extendTestLinear_tensor, extendTestHom_tensor, extendTestHom_tensor,
      extendTestLinear_tensor, hL]
  exact LinearMap.congr_fun heq f

theorem tensor_intertwiner_factors {J : Type*}
    (H : J → TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (hSchur : ∀ A : TestSections.Realization.lcCompactSpace X →ₗ[ℂ] TestSections.Realization.lcCompactSpace X,
      (∀ i f, A (H i f) = H i (A f)) → ∃ c : ℂ, ∀ f, A f = c • f)
    (φ : J → J) (L : TestSections.Realization.lcCompactSpace X ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace X)
    (hL : ∀ i f, L (H i f) = H (φ i) (L f))
    (U : TestSections.Realization.lcCompactSpace (X × Y) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (X × Y))
    (hU : ∀ i f, U (extendTestLinear (H i) f) = extendTestLinear (H (φ i)) (U f))
    (f₀ : TestSections.Realization.lcCompactSpace X) (x₀ : X) (hf₀ : f₀.val x₀ = 1) :
    ∃ V : TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace Y,
      ∀ f g, U (tensorTest f g) = tensorTest (L f) (V g) := by
  let T := extendTestHom (Y := Y) L
  let W := U.trans T.symm
  have hTW (f : TestSections.Realization.lcCompactSpace (X × Y)) : T (W f) = U f := T.apply_symm_apply _
  have hW i f : W (extendTestLinear (H i) f) = extendTestLinear (H i) (W f) := by
    apply T.injective
    rw [hTW, hU]
    change _ = extendTestHom L (extendTestLinear (H i) (W f))
    rw [extendTestHom_intertwines H φ L hL]
    exact congrArg (extendTestLinear (H (φ i))) (hTW f).symm
  obtain ⟨V, hV, _⟩ := local_commutant_equiv_factors H hSchur W hW f₀ x₀ hf₀
  refine ⟨V, ?_⟩
  intro f g
  calc
    U (tensorTest f g) = T (W (tensorTest f g)) := (hTW _).symm
    _ = T (rightTestHom V (tensorTest f g)) := congrArg (fun A => T (A (tensorTest f g))) hV
    _ = tensorTest (L f) (V g) := by
      rw [rightTestHom_tensor]
      exact extendTestHom_tensor L f (V g)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization
