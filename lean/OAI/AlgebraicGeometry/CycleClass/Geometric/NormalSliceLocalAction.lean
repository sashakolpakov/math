import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPair
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalDerivativeHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalBlock

/-! # Normal Slice Local Action -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSliceLocalAction.Cycles

noncomputable section

/-!
# Normal slices and actual local normal-class actions

The relative action of a genuine map of product pairs becomes the action of
its normal slice after the actual projection and section equivalences. On
small product neighborhoods this reduces nonlinear coordinate invariance to
the proved comparison of a differentiable germ with its derivative.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open scoped _root_.Topology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem relativeMap_congr {X Y : TopCat.{0}} {A : Set X} {B : Set Y}
    {u v : X ⟶ Y} (h : u = v) (hu : Set.MapsTo u A B) (hv : Set.MapsTo v A B) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomologyMap u hu n = LocalHomology.Cycles.relativeSingularHomologyMap v hv n := by
  subst v
  rfl

section ProductSlice

variable {E F E' F' : Type} [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace E'] [TopologicalSpace F']

/-- Restrict a product map to a tangential section and project its normal
coordinate. This is the actual continuous normal slice. -/
def normalSliceMap (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F')) (e : E) :
    TopCat.of F ⟶ TopCat.of F' :=
  NormalProductPair.Cycles.normalProductSection E F e ≫ φ ≫ NormalProductPair.Cycles.normalProductProjection E' F'

@[simp]
theorem normalSliceMap_apply (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F'))
    (e : E) (y : F) : normalSliceMap φ e y = (φ (e, y)).2 := rfl

theorem normalSliceMap_mapsTo (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F'))
    (e : E) (z : F) (z' : F')
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E F z) (NormalProductPair.Cycles.normalProductComplement E' F' z')) :
    Set.MapsTo (normalSliceMap φ e) ({z}ᶜ : Set F) ({z'}ᶜ : Set F') :=
  fun _ hy => hφ hy

/-- The product-to-slice identity already holds for the genuine relative
chain maps, before passing to homology. -/
theorem normalSlice_relativeChains (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F'))
    (e : E) (z : F) (z' : F')
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E F z) (NormalProductPair.Cycles.normalProductComplement E' F' z')) :
    NormalProductPair.Cycles.normalProductRelativeSection E F e z ≫ LocalHomology.Cycles.relativeSingularChainsMap φ hφ ≫
        NormalProductPair.Cycles.normalProductRelativeProjection E' F' z' =
      LocalHomology.Cycles.relativeSingularChainsMap (normalSliceMap φ e) (normalSliceMap_mapsTo φ e z z' hφ) := by
  simp only [NormalProductPair.Cycles.normalProductRelativeSection, NormalProductPair.Cycles.normalProductRelativeProjection,
    LocalHomology.Cycles.relativeSingularChainsMap_comp]
  rfl

/-- The exact normal-slice action on genuine relative singular homology. -/
theorem normalSlice_relativeHomology (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F'))
    (e : E) (z : F) (z' : F')
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E F z) (NormalProductPair.Cycles.normalProductComplement E' F' z'))
    (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomologyMap (NormalProductPair.Cycles.normalProductSection E F e)
        (NormalProductPair.Cycles.normalProductSection_mapsTo E F e z) n ≫
      LocalHomology.Cycles.relativeSingularHomologyMap φ hφ n ≫
        LocalHomology.Cycles.relativeSingularHomologyMap (NormalProductPair.Cycles.normalProductProjection E' F')
          (NormalProductPair.Cycles.normalProductProjection_mapsTo E' F' z') n =
      LocalHomology.Cycles.relativeSingularHomologyMap (normalSliceMap φ e) (normalSliceMap_mapsTo φ e z z' hφ) n := by
  rw [LocalHomology.Cycles.relativeSingularHomologyMap_comp, LocalHomology.Cycles.relativeSingularHomologyMap_comp]
  rfl

/-- Conjugating by the actual product equivalences gives precisely the
normal slice, for any displayed genuine tangential contractions. -/
theorem normalProductHomology_conjugate_of_contractions
    (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F'))
    (e : E) (e' : E') (z : F) (z' : F')
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (H' : ContinuousMap.Homotopy (ContinuousMap.const E' e') (ContinuousMap.id E'))
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E F z) (NormalProductPair.Cycles.normalProductComplement E' F' z'))
    (n : ℕ) :
    (NormalProductPair.Cycles.normalProductHomologyIsoOfContraction E F e z H n).inv ≫
        LocalHomology.Cycles.relativeSingularHomologyMap φ hφ n ≫
          (NormalProductPair.Cycles.normalProductHomologyIsoOfContraction E' F' e' z' H' n).hom =
      LocalHomology.Cycles.relativeSingularHomologyMap (normalSliceMap φ e) (normalSliceMap_mapsTo φ e z z' hφ) n :=
  normalSlice_relativeHomology φ e z z' hφ n

end ProductSlice

section LinearSlice

variable {E E' F F' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace F] [TopologicalSpace F']

/-- In linear tangential coordinates the conjugate map is literally
`y ↦ snd (φ (0,y))`, with no linearity condition on the product map. -/
theorem normalProductHomology_conjugate
    (φ : TopCat.of (E × F) ⟶ TopCat.of (E' × F')) (z : F) (z' : F')
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E F z) (NormalProductPair.Cycles.normalProductComplement E' F' z'))
    (n : ℕ) :
    (NormalProductPair.Cycles.normalProductHomologyIso E F z n).inv ≫ LocalHomology.Cycles.relativeSingularHomologyMap φ hφ n ≫
        (NormalProductPair.Cycles.normalProductHomologyIso E' F' z' n).hom =
      LocalHomology.Cycles.relativeSingularHomologyMap (normalSliceMap φ 0) (normalSliceMap_mapsTo φ 0 z z' hφ) n :=
  normalSlice_relativeHomology φ 0 z z' hφ n

end LinearSlice

section BallSlice

variable {E E' F F' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [TopologicalSpace F']

/-- For a product of two genuine open balls, normal excision is the only
additional factor in the same exact conjugacy identity. -/
theorem normalOpenProductBallsHomology_conjugate
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (φ : TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s) ⟶
      TopCat.of (E' × F')) (z' : F')
    (hφ : Set.MapsTo φ
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
        (LocalDerivativeHomology.Cycles.ballZero F s hs)) (NormalProductPair.Cycles.normalProductComplement E' F' z')) (n : ℕ) :
    (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E F r s hr hs n).inv ≫
        LocalHomology.Cycles.relativeSingularHomologyMap φ hφ n ≫ (NormalProductPair.Cycles.normalProductHomologyIso E' F' z' n).hom =
      (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of F) (Metric.ball 0 s) 0
        (Metric.mem_ball_self hs) Metric.isOpen_ball n).inv ≫
        LocalHomology.Cycles.relativeSingularHomologyMap (normalSliceMap φ (LocalDerivativeHomology.Cycles.ballZero E r hr))
          (normalSliceMap_mapsTo φ (LocalDerivativeHomology.Cycles.ballZero E r hr) (LocalDerivativeHomology.Cycles.ballZero F s hs) z' hφ) n := by
  change ((LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of F) (Metric.ball 0 s) 0
      (Metric.mem_ball_self hs) Metric.isOpen_ball n).inv ≫
        (NormalProductPair.Cycles.normalProductHomologyIsoOfContraction (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
          (LocalDerivativeHomology.Cycles.ballZero E r hr) (LocalDerivativeHomology.Cycles.ballZero F s hs)
          (NormalProductPair.Cycles.normalConvexContraction E (Metric.ball 0 r) (convex_ball 0 r)
            (Metric.mem_ball_self hr)) n).inv) ≫ _ ≫ _ = _
  rw [Category.assoc]
  congr 1
  exact normalSlice_relativeHomology φ (LocalDerivativeHomology.Cycles.ballZero E r hr) (LocalDerivativeHomology.Cycles.ballZero F s hs) z' hφ n

end BallSlice

/-- The explicit complex-matrix homotopy of product pairs also proves
complex-linear invariance in all degrees, including dimension zero. -/
theorem complexLinearLocalHomologyMap_eq_id_all {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ)) (n : ℕ) :
    LocalDerivativeHomology.Cycles.linearLocalHomologyMap (L.restrictScalars ℝ) n = 𝟙 _ := by
  let A := LinearMap.toMatrix' L.toLinearEquiv.toLinearMap
  have hA : IsUnit A :=
    LinearMap.isUnit_toMatrix'_iff.mpr ((Module.End.isUnit_iff _).mpr L.bijective)
  have h := normalProductHomology_conjugate
    (NormalProductPair.Cycles.normalProductComplexChange ℝ A) 0 0 (NormalProductPair.Cycles.normalProductComplexChange_mapsTo ℝ A hA) n
  rw [NormalProductPair.Cycles.normalProductComplexChange_homology_eq_id ℝ A hA n, Category.id_comp,
    Iso.inv_hom_id] at h
  have hs : normalSliceMap (NormalProductPair.Cycles.normalProductComplexChange ℝ A) 0 =
      LocalDerivativeHomology.Cycles.linearNormalMap (L.restrictScalars ℝ) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact LinearMap.toMatrix'_mulVec L.toLinearEquiv.toLinearMap x
  exact (relativeMap_congr hs
    (normalSliceMap_mapsTo (NormalProductPair.Cycles.normalProductComplexChange ℝ A) 0 0 0
      (NormalProductPair.Cycles.normalProductComplexChange_mapsTo ℝ A hA))
    (LocalDerivativeHomology.Cycles.linearNormalMap_preservesPuncture (L.restrictScalars ℝ)) n).symm.trans h.symm

section BallMaps

variable {E F E' F' : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace E'] [TopologicalSpace F']

/-- Restrict an actual locally continuous product map to a product of open
balls, with its genuine continuous-map structure. -/
def normalProductBallMap (Φ : E × F → E' × F') (r s : ℝ)
    (hc : ContinuousOn Φ (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) s)) :
    TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s) ⟶ TopCat.of (E' × F') :=
  TopCat.ofHom
    ⟨fun x => Φ (x.1.val, x.2.val), hc.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun x => ⟨x.1.property, x.2.property⟩)⟩

/-- The local geometric complement condition supplies an actual map of pairs. -/
theorem normalProductBallMap_mapsTo (Φ : E × F → E' × F') (r s : ℝ) (hs : 0 < s)
    (hc : ContinuousOn Φ (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) s)) (z' : F')
    (hpair : ∀ x ∈ Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) s,
      x.2 ≠ 0 → (Φ x).2 ≠ z') :
    Set.MapsTo (normalProductBallMap Φ r s hc)
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
        (LocalDerivativeHomology.Cycles.ballZero F s hs)) (NormalProductPair.Cycles.normalProductComplement E' F' z') := by
  intro x hx
  exact hpair _ ⟨x.1.property, x.2.property⟩ (fun h => hx (Subtype.ext h))

end BallMaps

section LocalComplexSlice

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] {p : ℕ}

omit [NormedSpace ℝ E] [NormedSpace ℝ E'] in
/-- When the normal slice fixes the origin, it equals the translated map
used by the actual derivative homotopy. -/
theorem normalProductBallMap_slice_eq_translated
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ)) (r s : ℝ) (hr : 0 < r)
    (hc : ContinuousOn Φ (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s))
    (hzero : (Φ (0, 0)).2 = 0)
    (hslice : ContinuousOn (fun y => (Φ (0, y)).2) (Metric.ball (0 : Fin p → ℂ) s)) :
    normalSliceMap (normalProductBallMap Φ r s hc) (LocalDerivativeHomology.Cycles.ballZero E r hr) =
      LocalDerivativeHomology.Cycles.translatedBallMap (fun y => (Φ (0, y)).2) s hslice := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (Φ (0, x.val)).2 = (Φ (0, x.val)).2 - (Φ (0, 0)).2
  rw [hzero, sub_zero]

/-- A checked derivative remainder bound gives identity normal action on
the actual product-ball pair, in every homology degree. -/
theorem normalProductBallMap_action_eq_id
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ)) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hc : ContinuousOn Φ (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s))
    (hpair : ∀ x ∈ Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s,
      x.2 ≠ 0 → (Φ x).2 ≠ 0)
    (hzero : (Φ (0, 0)).2 = 0) (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hslice : ContinuousOn (fun y => (Φ (0, y)).2) (Metric.ball (0 : Fin p → ℂ) s))
    (he : ∀ y, ‖y‖ < s → ‖(Φ (0, y)).2 - (Φ (0, 0)).2 - L y‖ ≤
      (1 / 2 : ℝ) * ‖L y‖) (n : ℕ) :
    (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs n).inv ≫
        LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s hc)
          (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair) n ≫
            (NormalProductPair.Cycles.normalProductHomologyIso E' (Fin p → ℂ) 0 n).hom = 𝟙 _ := by
  rw [normalOpenProductBallsHomology_conjugate]
  have hmap : LocalHomology.Cycles.relativeSingularHomologyMap
      (normalSliceMap (normalProductBallMap Φ r s hc) (LocalDerivativeHomology.Cycles.ballZero E r hr))
      (normalSliceMap_mapsTo (normalProductBallMap Φ r s hc) (LocalDerivativeHomology.Cycles.ballZero E r hr)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs) 0
        (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair)) n =
      LocalDerivativeHomology.Cycles.translatedBallLocalHomologyMap (fun y => (Φ (0, y)).2)
        (L.restrictScalars ℝ) s hs hslice he n := by
    unfold LocalDerivativeHomology.Cycles.translatedBallLocalHomologyMap
    exact relativeMap_congr
      (normalProductBallMap_slice_eq_translated Φ r s hr hc hzero hslice)
      (normalSliceMap_mapsTo (normalProductBallMap Φ r s hc) (LocalDerivativeHomology.Cycles.ballZero E r hr)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs) 0
        (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair))
      (LocalDerivativeHomology.Cycles.translatedBallMap_preservesPuncture (fun y => (Φ (0, y)).2)
        (L.restrictScalars ℝ) s hs hslice he) n
  rw [hmap, LocalDerivativeHomology.Cycles.translatedBallLocalHomologyMap_eq_excision_comp,
    complexLinearLocalHomologyMap_eq_id_all, Category.comp_id, Iso.inv_hom_id]

/-- A genuinely defined local product map with invertible complex normal
derivative acts identically on normal local homology after shrinking to
actual product balls. The radii and the derivative remainder bound are proved. -/
theorem exists_normalProductBallMap_action_eq_id
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ))
    (W : Set (E × (Fin p → ℂ))) (hW : W ∈ 𝓝 (0, 0)) (hΦ : ContinuousOn Φ W)
    (hpair : ∀ x ∈ W, x.2 ≠ 0 → (Φ x).2 ≠ 0) (hzero : (Φ (0, 0)).2 = 0)
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hderiv : HasFDerivAt (fun y => (Φ (0, y)).2)
      ((L.restrictScalars ℝ) : _ →L[ℝ] _) 0) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W),
      ∀ n : ℕ,
        (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs n).inv ≫
          LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s (hΦ.mono hsub))
            (normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
              (fun x hx => hpair x (hsub hx))) n ≫
            (NormalProductPair.Cycles.normalProductHomologyIso E' (Fin p → ℂ) 0 n).hom = 𝟙 _ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hW
  have hprod : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) r ⊆ W := by
    rw [ball_prod_same]
    exact hball
  have hsmall : {y | ‖(Φ (0, y)).2 - (Φ (0, 0)).2 - L y‖ ≤
      (1 / 2 : ℝ) * ‖L y‖} ∈ 𝓝 (0 : Fin p → ℂ) :=
    DerivativePuncturedHomotopy.Cycles.eventually_derivative_remainder_small (L.restrictScalars ℝ) hderiv
  obtain ⟨s, hs, hsball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (Metric.ball_mem_nhds (0 : Fin p → ℂ) hr) hsmall)
  have hnormal : Metric.ball (0 : Fin p → ℂ) s ⊆ Metric.ball 0 r :=
    fun _ hy => (hsball hy).1
  have hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W :=
    (Set.prod_mono Subset.rfl hnormal).trans hprod
  have hslice : ContinuousOn (fun y => (Φ (0, y)).2) (Metric.ball (0 : Fin p → ℂ) s) :=
    (hΦ.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hy => hsub ⟨Metric.mem_ball_self hr, hy⟩)).snd
  have he : ∀ y, ‖y‖ < s → ‖(Φ (0, y)).2 - (Φ (0, 0)).2 - L y‖ ≤
      (1 / 2 : ℝ) * ‖L y‖ := by
    intro y hy
    exact (hsball (by simpa only [Metric.mem_ball, dist_zero_right] using hy)).2
  refine ⟨r, s, hr, hs, hsub, fun n => ?_⟩
  exact normalProductBallMap_action_eq_id Φ r s hr hs (hΦ.mono hsub)
    (fun x hx => hpair x (hsub hx)) hzero L hslice he n

/-- The normalized normal class on a product of coordinate balls, obtained
from the actual product/excision isomorphism and the existing normal generator. -/
def complexNormalOpenProductBallsClass (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    LocalHomology.Cycles.relativeSingularHomology
      (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s))
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs)) (2 * p) :=
  (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs (2 * p)).inv
    ((ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1)

/-- Identity of the actual conjugated normal action implies preservation of
the already normalized normal class, rather than just a rank-one statement. -/
theorem normalProductBallMap_class_of_action
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ)) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hc : ContinuousOn Φ (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s))
    (hpair : ∀ x ∈ Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s,
      x.2 ≠ 0 → (Φ x).2 ≠ 0)
    (hact : (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs (2 * p)).inv ≫
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s hc)
        (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair) (2 * p) ≫
        (NormalProductPair.Cycles.normalProductHomologyIso E' (Fin p → ℂ) 0 (2 * p)).hom = 𝟙 _) :
    LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s hc)
      (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair) (2 * p)
        (complexNormalOpenProductBallsClass E p r s hr hs) = NormalProductPair.Cycles.complexNormalProductClass E' p := by
  have hm : (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs (2 * p)).inv ≫
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s hc)
        (normalProductBallMap_mapsTo Φ r s hs hc 0 hpair) (2 * p) =
      (NormalProductPair.Cycles.normalProductHomologyIso E' (Fin p → ℂ) 0 (2 * p)).inv := by
    apply (cancel_mono (NormalProductPair.Cycles.normalProductHomologyIso E' (Fin p → ℂ) 0 (2 * p)).hom).mp
    rw [Category.assoc, Iso.inv_hom_id]
    exact hact
  exact ConcreteCategory.congr_hom hm ((ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1)

/-- A local nonlinear coordinate change with invertible complex normal
derivative preserves the normalized normal class on a proved smaller product. -/
theorem exists_normalProductBallMap_class_invariant
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ))
    (W : Set (E × (Fin p → ℂ))) (hW : W ∈ 𝓝 (0, 0)) (hΦ : ContinuousOn Φ W)
    (hpair : ∀ x ∈ W, x.2 ≠ 0 → (Φ x).2 ≠ 0) (hzero : (Φ (0, 0)).2 = 0)
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hderiv : HasFDerivAt (fun y => (Φ (0, y)).2)
      ((L.restrictScalars ℝ) : _ →L[ℝ] _) 0) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W),
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s (hΦ.mono hsub))
        (normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
          (fun x hx => hpair x (hsub hx))) (2 * p)
        (complexNormalOpenProductBallsClass E p r s hr hs) = NormalProductPair.Cycles.complexNormalProductClass E' p := by
  obtain ⟨r, s, hr, hs, hsub, hact⟩ :=
    exists_normalProductBallMap_action_eq_id Φ W hW hΦ hpair hzero L hderiv
  exact ⟨r, s, hr, hs, hsub, normalProductBallMap_class_of_action Φ r s hr hs
    (hΦ.mono hsub) (fun x hx => hpair x (hsub hx)) (hact (2 * p))⟩

end LocalComplexSlice

section NormalBlockDerivative

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : ℕ}

/-- The normal slice derivative is the genuine normal block of the ambient
derivative. Its invertibility was proved from both horizontal preservation laws. -/
theorem normalSlice_hasFDerivAt_normalBlock
    (Φ : E × (Fin p → ℂ) → E × (Fin p → ℂ))
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (E × (Fin p → ℂ)))
    (hL : ∀ x : E, (L (x, 0)).2 = 0) (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0)
    (hderiv : HasFDerivAt Φ L.toContinuousLinearMap (0, 0)) :
    HasFDerivAt (fun y => (Φ (0, y)).2)
      (((ComplexNormalBlock.Cycles.normalBlock L hL hLi).restrictScalars ℝ) : _ →L[ℝ] _) 0 := by
  have h : HasFDerivAt (fun y => (Φ (0, y)).2) (ComplexNormalBlock.Cycles.normalBlock L hL hLi).toContinuousLinearMap 0 := by
    simpa only [ComplexNormalBlock.Cycles.normalBlock_toContinuousLinearMap, ContinuousLinearMap.inr_apply,
      Function.comp_def] using
      (hderiv.comp 0 (ContinuousLinearMap.inr ℂ E (Fin p → ℂ)).hasFDerivAt).snd
  exact h.restrictScalars ℝ

end NormalBlockDerivative

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] {p : ℕ}

/-- An actual nonlinear normal-coordinate change with an invertible
plane-preserving complex ambient derivative preserves the normalized normal
class after a proved product-neighborhood shrinking. -/
theorem exists_normalCoordinate_class_invariant
    (Φ : E × (Fin p → ℂ) → E × (Fin p → ℂ))
    (W : Set (E × (Fin p → ℂ))) (hW : W ∈ 𝓝 (0, 0)) (hΦ : ContinuousOn Φ W)
    (hpair : ∀ x ∈ W, x.2 ≠ 0 → (Φ x).2 ≠ 0) (hzero : (Φ (0, 0)).2 = 0)
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (E × (Fin p → ℂ)))
    (hL : ∀ x : E, (L (x, 0)).2 = 0) (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0)
    (hderiv : HasFDerivAt Φ L.toContinuousLinearMap (0, 0)) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W),
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductBallMap Φ r s (hΦ.mono hsub))
        (normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
          (fun x hx => hpair x (hsub hx))) (2 * p)
        (complexNormalOpenProductBallsClass E p r s hr hs) = NormalProductPair.Cycles.complexNormalProductClass E p :=
  exists_normalProductBallMap_class_invariant Φ W hW hΦ hpair hzero (ComplexNormalBlock.Cycles.normalBlock L hL hLi)
    (normalSlice_hasFDerivAt_normalBlock Φ L hL hLi hderiv)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSliceLocalAction.Cycles
