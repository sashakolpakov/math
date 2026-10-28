import OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedBall
import OAI.AlgebraicGeometry.CycleClass.Geometric.ConvexComplement
import OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf

/-! # Convex Support Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles

noncomputable section

/-!
# Relative homology and normalized classes with compact convex support

All maps are induced by the identity between the actual complementary
topological pairs. Restricting the class of a containing coordinate ball
already gives a normalized class for any compact support. Convexity will
identify its relative homology with point-local homology, giving uniqueness
and concentration in the top degree.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Restriction of supports commutes with restriction to any point of the smaller support. -/
@[reassoc]
theorem relativeComplementHomologyRestriction_toPoint (X : TopCat.{0})
    {K L : Set X} (hKL : K ⊆ L) (x : X) (hx : x ∈ K) (n : ℕ) :
    HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKL) n ≫
        LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X L x (hKL hx) n := by
  unfold LocalHomologyPresheaf.Cycles.localHomologyToPoint
  rw [← HomologicalComplex.homologyMap_comp, LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction_toPoint]

variable (E : Type) [NormedAddCommGroup E]

/-- A compact support is contained in a positive-radius closed ball about the origin. -/
theorem compactSupport_exists_pos_radius (K : Set E) (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ K ⊆ Metric.closedBall (0 : E) r :=
  hK.isBounded.subset_closedBall_lt 0 0

/-- A fixed containing radius for a compact support. -/
def compactSupportRadius (K : Set E) (hK : IsCompact K) : ℝ :=
  (compactSupport_exists_pos_radius E K hK).choose

theorem compactSupportRadius_pos (K : Set E) (hK : IsCompact K) :
    0 < compactSupportRadius E K hK :=
  (compactSupport_exists_pos_radius E K hK).choose_spec.1

theorem compactSupport_subset_closedBall (K : Set E) (hK : IsCompact K) :
    K ⊆ Metric.closedBall (0 : E) (compactSupportRadius E K hK) :=
  (compactSupport_exists_pos_radius E K hK).choose_spec.2

/-- On a closed ball, the existing support-to-point map is the closed-ball restriction. -/
theorem localHomologyToPoint_closedBall (r : ℝ) (x : E)
    (hx : x ∈ Metric.closedBall (0 : E) r) (n : ℕ) :
    LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of E) (Metric.closedBall (0 : E) r) x hx n =
      ClosedBall.Cycles.closedBallPointHomologyMap E r x hx n := rfl

/-- Restricting a containing coordinate-ball class gives a class with any compact support. -/
def complexCompactSupportClass (p : ℕ) (K : Set (Fin p → ℂ)) (hK : IsCompact K) :
    HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin p → ℂ)) K (2 * p) :=
  HomologicalComplex.homologyMap
    (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction (TopCat.of (Fin p → ℂ))
      (compactSupport_subset_closedBall (Fin p → ℂ) K hK)) (2 * p)
    (ClosedBall.Cycles.complexClosedBallClass p (compactSupportRadius (Fin p → ℂ) K hK)
      (compactSupportRadius_pos (Fin p → ℂ) K hK).le)

/-- The compact-support class restricts to the specified coordinate orientation at every point. -/
theorem complexCompactSupportClass_atPoint (p : ℕ) (K : Set (Fin p → ℂ))
    (hK : IsCompact K) (x : Fin p → ℂ) (hx : x ∈ K) :
    LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) K x hx (2 * p)
        (complexCompactSupportClass p K hK) = ClosedBall.Cycles.complexCoordinatePointClass p x := by
  let r := compactSupportRadius (Fin p → ℂ) K hK
  have hr : 0 ≤ r := (compactSupportRadius_pos (Fin p → ℂ) K hK).le
  have hKR : K ⊆ Metric.closedBall (0 : Fin p → ℂ) r :=
    compactSupport_subset_closedBall (Fin p → ℂ) K hK
  change LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) K x hx (2 * p)
      (HomologicalComplex.homologyMap
        (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction (TopCat.of (Fin p → ℂ)) hKR) (2 * p)
        (ClosedBall.Cycles.complexClosedBallClass p r hr)) = _
  calc
    _ = LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ))
        (Metric.closedBall (0 : Fin p → ℂ) r) x (hKR hx) (2 * p)
        (ClosedBall.Cycles.complexClosedBallClass p r hr) :=
      ConcreteCategory.congr_hom
        (relativeComplementHomologyRestriction_toPoint
          (TopCat.of (Fin p → ℂ)) hKR x hx (2 * p)) _
    _ = _ := ClosedBall.Cycles.complexClosedBallClass_atPoint p r hr x (hKR hx)

variable [NormedSpace ℝ E]

/-- For compact convex support, the actual restriction to any supported point is
a quasi-isomorphism. This is the comparison of the two short exact sequences
of actual singular chains, using the complement homotopy equivalence. -/
theorem convexSupportPointChainMap_quasiIso (K : Set E) (hK : IsCompact K)
    (hconv : Convex ℝ K) (x : E) (hx : x ∈ K) :
    QuasiIso (LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint (TopCat.of E) K x hx) := by
  let hm : Set.MapsTo (𝟙 (TopCat.of E)) Kᶜ ({x}ᶜ : Set E) := by
    intro y hy
    change y ≠ x
    intro hyx
    exact hy (hyx.symm ▸ hx)
  let φ := RelativeHomologyExact.Cycles.relativeChainSequenceMap (𝟙 (TopCat.of E)) hm
  apply HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (LocalHomology.Cycles.relativeChainSequence_shortExact (TopCat.of E) Kᶜ)
    (LocalHomology.Cycles.relativeChainSequence_shortExact (TopCat.of E) ({x}ᶜ : Set E))
  · change QuasiIso (LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of E)) hm))
    have hinc : LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of E)) hm =
        TopCat.ofHom (ConvexComplement.Cycles.convexComplementHomotopyEquiv K x hK hconv hx).toFun := by
      rw [ConvexComplement.Cycles.convexComplementHomotopyEquiv_toFun]
      rfl
    rw [hinc]
    exact (ContractibleModel.Cycles.singularChainsHomotopyEquiv (ModuleCat.of ℤ ℤ)
      (X := TopCat.of (Kᶜ : Set E)) (Y := TopCat.of ({x}ᶜ : Set E))
      (ConvexComplement.Cycles.convexComplementHomotopyEquiv K x hK hconv hx)).quasiIso_hom
  · change QuasiIso (LocalHomology.Cycles.integralSingularChainFunctor.map (𝟙 (TopCat.of E)))
    rw [CategoryTheory.Functor.map_id]
    infer_instance

/-- Relative homology with compact convex support is the actual local homology
at every point of that support. -/
def convexSupportPointHomologyIso (K : Set E) (hK : IsCompact K)
    (hconv : Convex ℝ K) (x : E) (hx : x ∈ K) (n : ℕ) :
    HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of E) K n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of E) x n := by
  have := convexSupportPointChainMap_quasiIso E K hK hconv x hx
  exact isoOfQuasiIsoAt (LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint (TopCat.of E) K x hx) n

@[simp]
theorem convexSupportPointHomologyIso_hom (K : Set E) (hK : IsCompact K)
    (hconv : Convex ℝ K) (x : E) (hx : x ∈ K) (n : ℕ) :
    (convexSupportPointHomologyIso E K hK hconv x hx n).hom =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of E) K x hx n := rfl

/-- In particular, the existing point restriction map is bijective in every degree. -/
theorem convexSupportPointHomologyMap_bijective (K : Set E) (hK : IsCompact K)
    (hconv : Convex ℝ K) (x : E) (hx : x ∈ K) (n : ℕ) :
    Function.Bijective (LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of E) K x hx n) :=
  ConcreteCategory.bijective_of_isIso (convexSupportPointHomologyIso E K hK hconv x hx n).hom

/-- Top homology with nonempty compact convex support in a complex coordinate
space is `ℤ`, with the prescribed coordinate normalization at a supported point. -/
def complexConvexSupportTopHomologyIso (p : ℕ) (K : Set (Fin p → ℂ))
    (hK : IsCompact K) (hconv : Convex ℝ K) (x : Fin p → ℂ) (hx : x ∈ K) :
    HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin p → ℂ)) K (2 * p) ≅ ModuleCat.of ℤ ℤ :=
  convexSupportPointHomologyIso (Fin p → ℂ) K hK hconv x hx (2 * p) ≪≫
    ClosedBall.Cycles.complexCoordinatePointHomologyIso p x

/-- The compact-support class maps to one under the actual normalized top-homology isomorphism. -/
theorem complexConvexSupportTopHomologyIso_class (p : ℕ) (K : Set (Fin p → ℂ))
    (hK : IsCompact K) (hconv : Convex ℝ K) (x : Fin p → ℂ) (hx : x ∈ K) :
    (complexConvexSupportTopHomologyIso p K hK hconv x hx).hom
        (complexCompactSupportClass p K hK) = 1 := by
  change (ClosedBall.Cycles.complexCoordinatePointHomologyIso p x).hom
    (LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) K x hx (2 * p)
      (complexCompactSupportClass p K hK)) = 1
  rw [complexCompactSupportClass_atPoint]
  exact ConcreteCategory.congr_hom (ClosedBall.Cycles.complexCoordinatePointHomologyIso p x).inv_hom_id 1

/-- All-point normalization uniquely determines the class on nonempty compact convex support. -/
theorem complexConvexSupportClass_unique (p : ℕ) (K : Set (Fin p → ℂ))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (a : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin p → ℂ)) K (2 * p))
    (ha : ∀ x (hx : x ∈ K),
      LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) K x hx (2 * p) a =
        ClosedBall.Cycles.complexCoordinatePointClass p x) :
    a = complexCompactSupportClass p K hK := by
  obtain ⟨x, hx⟩ := hne
  apply (convexSupportPointHomologyMap_bijective (Fin p → ℂ) K hK hconv x hx (2 * p)).1
  rw [ha x hx, complexCompactSupportClass_atPoint]

/-- The normalized class is the restriction of every containing closed-ball
class, so it is independent of the chosen containing radius. -/
theorem complexConvexSupportClass_eq_ballRestriction (p : ℕ) (K : Set (Fin p → ℂ))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (r : ℝ) (hr : 0 ≤ r) (hKR : K ⊆ Metric.closedBall (0 : Fin p → ℂ) r) :
    complexCompactSupportClass p K hK =
      HomologicalComplex.homologyMap
        (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction (TopCat.of (Fin p → ℂ)) hKR) (2 * p)
        (ClosedBall.Cycles.complexClosedBallClass p r hr) := by
  symm
  apply complexConvexSupportClass_unique p K hK hconv hne
  intro x hx
  calc
    _ = LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ))
        (Metric.closedBall (0 : Fin p → ℂ) r) x (hKR hx) (2 * p)
        (ClosedBall.Cycles.complexClosedBallClass p r hr) :=
      ConcreteCategory.congr_hom
        (relativeComplementHomologyRestriction_toPoint
          (TopCat.of (Fin p → ℂ)) hKR x hx (2 * p)) _
    _ = _ := ClosedBall.Cycles.complexClosedBallClass_atPoint p r hr x (hKR hx)

/-- Relative homology of nonempty compact convex support vanishes outside the real top degree. -/
theorem complexConvexSupportHomology_isZero (p : ℕ) (K : Set (Fin p → ℂ))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (n : ℕ) (hn : n ≠ 2 * p) :
    IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin p → ℂ)) K n) := by
  obtain ⟨x, hx⟩ := hne
  exact (ComplexLocalVanishing.Cycles.complexNormalLocalHomology_isZero p n hn).of_iso
    (convexSupportPointHomologyIso (Fin p → ℂ) K hK hconv x hx n ≪≫
      ClosedBall.Cycles.localTranslationHomologyIso (Fin p → ℂ) x n)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles
