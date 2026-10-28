import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalExcision
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearPuncturedHomotopy
import Mathlib.Analysis.Normed.Module.Convex

/-! # Normal Product Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPair

noncomputable section

/-!
# The actual normal product pair

Projection onto the normal coordinate and a constant tangential section are
inverse up to a homotopy that never changes the normal coordinate. For a real
normed tangential space, and for its convex neighborhoods, the contraction is
constructed explicitly. All relative chain and homology maps are the existing
maps of genuine singular pairs.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Matrix

set_option backward.isDefEq.respectTransparency false

namespace Cycles

section PointedProduct

variable (E F : Type) [TopologicalSpace E] [TopologicalSpace F]

/-- The complement of the normal zero section, for a pointed normal space. -/
def normalProductComplement (z : F) : Set (E × F) := {x | x.2 ≠ z}

omit [TopologicalSpace E] [TopologicalSpace F] in
theorem normalProductComplement_eq (z : F) :
    normalProductComplement E F z = ((Set.univ : Set E) ×ˢ {z})ᶜ := by
  ext x
  simp [normalProductComplement]

/-- Projection of the product onto its normal factor. -/
def normalProductProjection : TopCat.of (E × F) ⟶ TopCat.of F :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

/-- The section at a specified tangential point. -/
def normalProductSection (e : E) : TopCat.of F ⟶ TopCat.of (E × F) :=
  TopCat.ofHom ⟨fun y => (e, y), continuous_const.prodMk continuous_id⟩

theorem normalProductProjection_mapsTo (z : F) :
    Set.MapsTo (normalProductProjection E F) (normalProductComplement E F z) ({z}ᶜ : Set F) :=
  fun _ hx => hx

theorem normalProductSection_mapsTo (e : E) (z : F) :
    Set.MapsTo (normalProductSection E F e) ({z}ᶜ : Set F) (normalProductComplement E F z) :=
  fun _ hx => hx

@[simp]
theorem normalProductSection_projection (e : E) :
    normalProductSection E F e ≫ normalProductProjection E F = 𝟙 (TopCat.of F) := rfl

/-- Any displayed tangential contraction gives a product homotopy that
leaves the normal coordinate fixed. -/
def normalProductHomotopyOfContraction (e : E)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E)) :
    TopCat.Homotopy (normalProductProjection E F ≫ normalProductSection E F e)
      (𝟙 (TopCat.of (E × F))) where
  toFun q := (H (q.1, q.2.1), q.2.2)
  continuous_toFun :=
    (H.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd)
  map_zero_left x := by simp [normalProductProjection, normalProductSection]
  map_one_left x := by simp

@[simp]
theorem normalProductHomotopyOfContraction_snd (e : E)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (t : unitInterval) (x : E × F) :
    (normalProductHomotopyOfContraction E F e H (t, x)).2 = x.2 := rfl

theorem normalProductHomotopyOfContraction_mapsTo (e : E) (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (t : unitInterval) :
    Set.MapsTo (fun x => normalProductHomotopyOfContraction E F e H (t, x))
      (normalProductComplement E F z) (normalProductComplement E F z) :=
  fun _ hx => hx

/-- The actual map of relative chains induced by normal projection. -/
def normalProductRelativeProjection (z : F) :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of (E × F)) (normalProductComplement E F z) ⟶
      LocalHomology.Cycles.relativeSingularChains (TopCat.of F) ({z}ᶜ : Set F) :=
  LocalHomology.Cycles.relativeSingularChainsMap (normalProductProjection E F) (normalProductProjection_mapsTo E F z)

/-- The actual relative-chain map of the constant tangential section. -/
def normalProductRelativeSection (e : E) (z : F) :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of F) ({z}ᶜ : Set F) ⟶
      LocalHomology.Cycles.relativeSingularChains (TopCat.of (E × F)) (normalProductComplement E F z) :=
  LocalHomology.Cycles.relativeSingularChainsMap (normalProductSection E F e) (normalProductSection_mapsTo E F e z)

@[simp]
theorem normalProductRelativeSection_projection (e : E) (z : F) :
    normalProductRelativeSection E F e z ≫ normalProductRelativeProjection E F z = 𝟙 _ := by
  rw [normalProductRelativeSection, normalProductRelativeProjection,
    LocalHomology.Cycles.relativeSingularChainsMap_comp]
  change LocalHomology.Cycles.relativeSingularChainsMap (𝟙 (TopCat.of F))
    (A := ({z}ᶜ : Set F)) (B := ({z}ᶜ : Set F)) (fun _ hx => hx) = _
  exact LocalHomology.Cycles.relativeSingularChainsMap_id _ _

/-- A supplied genuine tangential contraction induces an actual relative-chain
homotopy equivalence. The next section constructs the contraction for linear models. -/
def normalProductChainEquivOfContraction (e : E) (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E)) :
    HomotopyEquiv
      (LocalHomology.Cycles.relativeSingularChains (TopCat.of (E × F)) (normalProductComplement E F z))
      (LocalHomology.Cycles.relativeSingularChains (TopCat.of F) ({z}ᶜ : Set F)) where
  hom := normalProductRelativeProjection E F z
  inv := normalProductRelativeSection E F e z
  homotopyHomInvId := by
    rw [normalProductRelativeProjection, normalProductRelativeSection, LocalHomology.Cycles.relativeSingularChainsMap_comp]
    have h := RelativeHomotopy.Cycles.relativeSingularChainsHomotopy
      (A := normalProductComplement E F z) (B := normalProductComplement E F z)
      (fun _ hx => hx) (fun _ hx => hx)
      (normalProductHomotopyOfContraction E F e H)
      (normalProductHomotopyOfContraction_mapsTo E F e z H)
    simpa only [LocalHomology.Cycles.relativeSingularChainsMap_id] using h
  homotopyInvHomId := Homotopy.ofEq (normalProductRelativeSection_projection E F e z)

/-- Homology of the product pair is homology of the normal pointed pair. -/
def normalProductHomologyIsoOfContraction (e : E) (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E)) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of (E × F)) (normalProductComplement E F z) n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of F) z n :=
  (normalProductChainEquivOfContraction E F e z H).toHomologyIso n

@[simp]
theorem normalProductHomologyIsoOfContraction_hom (e : E) (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E)) (n : ℕ) :
    (normalProductHomologyIsoOfContraction E F e z H n).hom =
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductProjection E F)
        (normalProductProjection_mapsTo E F z) n := rfl

@[simp]
theorem normalProductHomologyIsoOfContraction_inv (e : E) (z : F)
    (H : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E)) (n : ℕ) :
    (normalProductHomologyIsoOfContraction E F e z H n).inv =
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductSection E F e)
        (normalProductSection_mapsTo E F e z) n := rfl

end PointedProduct

section LinearTangent

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : Type) [TopologicalSpace F]

/-- The displayed linear contraction, from the zero section to the identity. -/
def normalLinearContraction :
    ContinuousMap.Homotopy (ContinuousMap.const E 0) (ContinuousMap.id E) where
  toFun q := (q.1 : ℝ) • q.2
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

/-- The full linear normal product pair is chain-homotopy equivalent to the
actual normal punctured pair, with no contractibility assumption left to prove. -/
def normalProductChainEquiv (z : F) :
    HomotopyEquiv
      (LocalHomology.Cycles.relativeSingularChains (TopCat.of (E × F)) (normalProductComplement E F z))
      (LocalHomology.Cycles.relativeSingularChains (TopCat.of F) ({z}ᶜ : Set F)) :=
  normalProductChainEquivOfContraction E F 0 z (normalLinearContraction E)

/-- The actual homology equivalence of the linear normal product model. -/
def normalProductHomologyIso (z : F) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of (E × F)) (normalProductComplement E F z) n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of F) z n :=
  (normalProductChainEquiv E F z).toHomologyIso n

@[simp]
theorem normalProductHomologyIso_hom (z : F) (n : ℕ) :
    (normalProductHomologyIso E F z n).hom =
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductProjection E F)
        (normalProductProjection_mapsTo E F z) n := rfl

@[simp]
theorem normalProductHomologyIso_inv (z : F) (n : ℕ) :
    (normalProductHomologyIso E F z n).inv =
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductSection E F 0)
        (normalProductSection_mapsTo E F 0 z) n := rfl

/-- Linear contraction inside an actual convex tangential neighborhood. -/
def normalConvexContraction (U : Set E) (hU : Convex ℝ U) (h0 : (0 : E) ∈ U) :
    ContinuousMap.Homotopy (ContinuousMap.const U ⟨0, h0⟩) (ContinuousMap.id U) where
  toFun q := ⟨(q.1 : ℝ) • q.2.val, hU.smul_mem_of_zero_mem h0 q.2.property q.1.property⟩
  continuous_toFun := by fun_prop
  map_zero_left x := by apply Subtype.ext; simp
  map_one_left x := by apply Subtype.ext; simp

/-- The corresponding normal-pair equivalence for a convex tangential neighborhood. -/
def normalConvexProductHomologyIso (U : Set E) (hU : Convex ℝ U) (h0 : (0 : E) ∈ U)
    (z : F) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of (U × F)) (normalProductComplement U F z) n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of F) z n :=
  normalProductHomologyIsoOfContraction U F ⟨0, h0⟩ z (normalConvexContraction E U hU h0) n

/-- Open tangential balls are an immediate genuine local product model. -/
def normalOpenBallProductHomologyIso (r : ℝ) (hr : 0 < r) (z : F) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Metric.ball (0 : E) r × F))
      (normalProductComplement (Metric.ball (0 : E) r) F z) n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of F) z n :=
  normalConvexProductHomologyIso E F (Metric.ball 0 r) (convex_ball 0 r)
    (Metric.mem_ball_self hr) z n

/-- The relative projection is independent of which tangential point is used
as the section: every such section induces its inverse on homology. -/
theorem normalProductHomologyIso_inv_eq_section (e : E) (z : F) (n : ℕ) :
    (normalProductHomologyIso E F z n).inv =
      LocalHomology.Cycles.relativeSingularHomologyMap (normalProductSection E F e)
        (normalProductSection_mapsTo E F e z) n := by
  apply (cancel_mono (normalProductHomologyIso E F z n).hom).mp
  rw [Iso.inv_hom_id, normalProductHomologyIso_hom, LocalHomology.Cycles.relativeSingularHomologyMap_comp]
  change 𝟙 _ = LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 (TopCat.of F))
    (A := ({z}ᶜ : Set F)) (B := ({z}ᶜ : Set F)) (fun _ hx => hx) n
  exact (LocalHomology.Cycles.relativeSingularHomologyMap_id _ _ _).symm

end LinearTangent

section TwoBalls

variable (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Both factors may be actual open balls. Normal projection followed by
proved local excision identifies their pair homology with the full normal model. -/
def normalOpenProductBallsHomologyIso (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology
      (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s))
      (normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
        ⟨0, Metric.mem_ball_self hs⟩) n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of F) 0 n :=
  normalOpenBallProductHomologyIso E (Metric.ball (0 : F) s) r hr
    ⟨0, Metric.mem_ball_self hs⟩ n ≪≫
      LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of F) (Metric.ball 0 s) 0
        (Metric.mem_ball_self hs) Metric.isOpen_ball n

end TwoBalls

section ComplexChange

variable (E : Type) [TopologicalSpace E]
variable {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (hA : IsUnit A)

/-- A complex linear change acts in the normal coordinate of the actual product. -/
def normalProductComplexChange : TopCat.of (E × (Fin p → ℂ)) ⟶ TopCat.of (E × (Fin p → ℂ)) :=
  TopCat.ofHom ⟨fun x => (x.1, A *ᵥ x.2), by fun_prop⟩

include hA in
theorem normalProductComplexChange_mapsTo :
    Set.MapsTo (normalProductComplexChange E A)
      (normalProductComplement E (Fin p → ℂ) 0) (normalProductComplement E (Fin p → ℂ) 0) :=
  fun _ hx => PuncturedLinearHomotopy.Cycles.complexMatrix_mulVec_ne_zero A hA hx

/-- The known path of invertible complex matrices gives an actual homotopy of
normal product pairs, keeping the tangential coordinate fixed. -/
def normalProductComplexChangeHomotopy :
    TopCat.Homotopy (𝟙 (TopCat.of (E × (Fin p → ℂ)))) (normalProductComplexChange E A) where
  toFun q := (q.2.1, ComplexLinearHomotopy.Cycles.complexMatrixPath A hA q.1 *ᵥ q.2.2)
  continuous_toFun :=
    (continuous_fst.comp continuous_snd).prodMk
      (((ComplexLinearHomotopy.Cycles.complexMatrixPath A hA).continuous.comp continuous_fst).matrix_mulVec
        (continuous_snd.comp continuous_snd))
  map_zero_left x := by simp
  map_one_left x := by simp [normalProductComplexChange]

theorem normalProductComplexChangeHomotopy_mapsTo (t : unitInterval) :
    Set.MapsTo (fun x => normalProductComplexChangeHomotopy E A hA (t, x))
      (normalProductComplement E (Fin p → ℂ) 0) (normalProductComplement E (Fin p → ℂ) 0) :=
  fun _ hx => PuncturedLinearHomotopy.Cycles.complexMatrix_mulVec_ne_zero _ (ComplexLinearHomotopy.Cycles.complexMatrixPath_isUnit A hA t) hx

/-- Complex normal coordinate changes act trivially on all relative homology
groups of the product pair, by the displayed homotopy of pairs. -/
theorem normalProductComplexChange_homology_eq_id (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomologyMap (normalProductComplexChange E A)
      (normalProductComplexChange_mapsTo E A hA) n = 𝟙 _ := by
  have h := RelativeHomotopy.Cycles.relativeSingularHomologyMap_eq_of_homotopy
    (A := normalProductComplement E (Fin p → ℂ) 0)
    (B := normalProductComplement E (Fin p → ℂ) 0)
    (fun _ hx => hx) (normalProductComplexChange_mapsTo E A hA)
    (normalProductComplexChangeHomotopy E A hA)
    (normalProductComplexChangeHomotopy_mapsTo E A hA) n
  simpa only [LocalHomology.Cycles.relativeSingularHomologyMap_id] using h.symm

end ComplexChange

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℕ)

/-- The genuine relative homology group in the complex normal orientation degree. -/
def complexNormalProductTopHomologyIso :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of (E × (Fin p → ℂ)))
      (normalProductComplement E (Fin p → ℂ) 0) (2 * p) ≅ ModuleCat.of ℤ ℤ :=
  normalProductHomologyIso E (Fin p → ℂ) 0 (2 * p) ≪≫ ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p

/-- The normal class transported by the genuine projection and section equivalence. -/
def complexNormalProductClass :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of (E × (Fin p → ℂ)))
      (normalProductComplement E (Fin p → ℂ) 0) (2 * p) :=
  (complexNormalProductTopHomologyIso E p).inv 1

@[simp]
theorem complexNormalProductClass_normalization :
    (complexNormalProductTopHomologyIso E p).hom (complexNormalProductClass E p) = 1 := by
  change ((complexNormalProductTopHomologyIso E p).inv ≫
    (complexNormalProductTopHomologyIso E p).hom) 1 = 1
  simp

theorem complexNormalProductClass_ne_zero : complexNormalProductClass E p ≠ 0 := by
  intro h
  have hn := complexNormalProductClass_normalization E p
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- The transported class is literally the image of the known normal class
under the zero-section map of relative pairs. -/
theorem complexNormalProductClass_eq_section :
    complexNormalProductClass E p =
      (LocalHomology.Cycles.relativeSingularHomologyMap (normalProductSection E (Fin p → ℂ) 0)
        (normalProductSection_mapsTo E (Fin p → ℂ) 0 0) (2 * p)).hom
          ((ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1) := rfl

/-- Normal projection recovers the previously constructed normal generator. -/
theorem complexNormalProductClass_projection :
    (LocalHomology.Cycles.relativeSingularHomologyMap (normalProductProjection E (Fin p → ℂ))
      (normalProductProjection_mapsTo E (Fin p → ℂ) 0) (2 * p)).hom
        (complexNormalProductClass E p) = (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1 := by
  change ((normalProductHomologyIso E (Fin p → ℂ) 0 (2 * p)).inv ≫
    (normalProductHomologyIso E (Fin p → ℂ) 0 (2 * p)).hom)
      ((ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1) = _
  rw [Iso.inv_hom_id]
  rfl

/-- The known complex normal class is unchanged by every invertible complex
normal coordinate change. -/
theorem complexNormalProductClass_invariant
    (A : Matrix (Fin p) (Fin p) ℂ) (hA : IsUnit A) :
    (LocalHomology.Cycles.relativeSingularHomologyMap (normalProductComplexChange E A)
      (normalProductComplexChange_mapsTo E A hA) (2 * p)).hom
        (complexNormalProductClass E p) = complexNormalProductClass E p := by
  rw [normalProductComplexChange_homology_eq_id E A hA]
  rfl

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPair
