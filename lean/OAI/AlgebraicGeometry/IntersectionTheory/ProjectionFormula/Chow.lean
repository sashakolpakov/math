import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cohomology
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowPullback
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.Chow
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Definitions

/-! # Chow -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Chow

noncomputable section

section

/-!
# ProjectionFormula: projection formula

The cohomological target below is proved with the exact PoincareData and
pushforward definitions of the specification. Full geometric moving proves
intersection and graph-pullback totality below. Intersection-preserving moving
also proves the exact bilinear Chow intersection map in every codimension.
Smooth product pullback preserves principal relations, giving the exact linear
graph pullback on Chow groups. Native etale support multiplicities, fiber
degrees, graph factorization, and component restriction prove the full Chow
projection identity for arbitrary smooth projective presentations.
-/

open _root_.CategoryTheory

namespace Construction

theorem projection_formula
    {X Y : TopCat.{0}}
    [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y]
    {m n : ℕ}
    (DX : Definitions.PoincareData X m) (DY : Definitions.PoincareData Y n)
    (f : X ⟶ Y)
    (p q s r t : ℕ)
    (hq : q + r = m)
    (hs : s + r = n)
    (hpq : (p + q) + t = m)
    (hps : (p + s) + t = n)
    (α : Definitions.HQ Y p) (β : Definitions.HQ X q) :
    Definitions.pushforward DX DY f (p + q) (p + s) t hpq hps
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) X p q
          (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f p α) β) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) Y p s α
        (Definitions.pushforward DX DY f q s r hq hs β) := by
  have hr : r = t + p := by omega
  subst r
  have hXouter : t + (p + q) = m := by omega
  have hXinner : (t + p) + q = m := by omega
  have hYouter : t + (p + s) = n := by omega
  have hYinner : (t + p) + s = n := by omega
  apply Cohomology.Construction.pairing_ext_right DY hYouter
  intro γ
  calc
    Cohomology.Construction.pairing DY hYouter γ
        (Definitions.pushforward DX DY f (p + q) (p + s) t hpq hps
          (Cohomology.Construction.cup X p q (Cohomology.Construction.pull f p α) β)) =
        Cohomology.Construction.pairing DX hXouter (Cohomology.Construction.pull f t γ) (Cohomology.Construction.cup X p q (Cohomology.Construction.pull f p α) β) :=
      Cohomology.Construction.pairing_pushforward DX DY f hpq hps hXouter hYouter γ _
    _ = Cohomology.Construction.pairing DX hXinner (Cohomology.Construction.cup X t p (Cohomology.Construction.pull f t γ) (Cohomology.Construction.pull f p α)) β :=
      (Cohomology.Construction.pairing_assoc DX hXinner hXouter (Cohomology.Construction.pull f t γ) (Cohomology.Construction.pull f p α) β).symm
    _ = Cohomology.Construction.pairing DX hXinner (Cohomology.Construction.pull f (t + p) (Cohomology.Construction.cup Y t p γ α)) β :=
      congrArg (fun z => Cohomology.Construction.pairing DX hXinner z β) (Cohomology.Construction.pull_cup f t p γ α).symm
    _ = Cohomology.Construction.pairing DY hYinner (Cohomology.Construction.cup Y t p γ α)
        (Definitions.pushforward DX DY f q s (t + p) hq hs β) :=
      (Cohomology.Construction.pairing_pushforward DX DY f hq hs hXinner hYinner (Cohomology.Construction.cup Y t p γ α) β).symm
    _ = Cohomology.Construction.pairing DY hYouter γ
        (Cohomology.Construction.cup Y p s α (Definitions.pushforward DX DY f q s (t + p) hq hs β)) :=
      Cohomology.Construction.pairing_assoc DY hYinner hYouter γ α _

end Construction

open _root_.AlgebraicGeometry

namespace Construction

theorem chow_intersection_total (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : ProperCycleLinearity.ChowQ X p) (b : ProperCycleLinearity.ChowQ X q) :
    (Definitions.chowIntersection X p q a b).Nonempty :=
  General.ChowMoving.chowIntersection_nonempty X m p q a b

theorem chow_intersection_map_exists (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] :
    ∃ I : ProperCycleLinearity.ChowQ X p →ₗ[ℚ] ProperCycleLinearity.ChowQ X q →ₗ[ℚ]
        ProperCycleLinearity.ChowQ X (p + q),
      ∀ a b, Definitions.chowIntersection X p q a b = {I a b} :=
  General.GeneralChowIntersection.chowIntersection_map_exists X m p q

theorem chow_pullback_total {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (P : ProperCycleLinearity.ProductPresentation X Y) (f : X.toOver ⟶ Y.toOver) (m n p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (a : ProperCycleLinearity.ChowQ Y p) : (Definitions.chowPullback P f n p a).Nonempty :=
  General.ChowMoving.GraphTotality.chowPullback_nonempty P f m n p a

theorem chow_pullback_map_exists {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (P : ProperCycleLinearity.ProductPresentation X Y) (f : X.toOver ⟶ Y.toOver) (m n p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap] :
    ∃ F : ProperCycleLinearity.ChowQ Y p →ₗ[ℚ] ProperCycleLinearity.ChowQ X p,
      ∀ a, Definitions.chowPullback P f n p a = {F a} :=
  General.ChowPullback.chowPullback_map_exists P f m n p

theorem chow_projection_formula
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (_hf : IsProper f.left)
    (P : ProperCycleLinearity.ProductPresentation X Y)
    (m n : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap]
    (p q s : ℕ)
    (hdeg : q + n = s + m)
    (hdegCup : (p + q) + n = (p + s) + m) :
    ∃ (intersectionX : ProperCycleLinearity.ChowQ X p →ₗ[ℚ]
          ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (p + q))
      (intersectionY : ProperCycleLinearity.ChowQ Y p →ₗ[ℚ]
          ProperCycleLinearity.ChowQ Y s →ₗ[ℚ] ProperCycleLinearity.ChowQ Y (p + s))
      (pull : ProperCycleLinearity.ChowQ Y p →ₗ[ℚ] ProperCycleLinearity.ChowQ X p)
      (pushQ : ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ Y s)
      (pushPQ : ProperCycleLinearity.ChowQ X (p + q) →ₗ[ℚ]
          ProperCycleLinearity.ChowQ Y (p + s)),
      (∀ a b, Definitions.chowIntersection X p q a b = {intersectionX a b}) ∧
      (∀ a b, Definitions.chowIntersection Y p s a b = {intersectionY a b}) ∧
      (∀ a, Definitions.chowPullback P f n p a = {pull a}) ∧
      (∀ b, Definitions.chowPushforward f q s b = {pushQ b}) ∧
      (∀ c, Definitions.chowPushforward f (p + q) (p + s) c = {pushPQ c}) ∧
      ∀ (α : ProperCycleLinearity.ChowQ Y p) (β : ProperCycleLinearity.ChowQ X q),
        pushPQ (intersectionX (pull α) β) = intersectionY α (pushQ β) := by
  refine ⟨General.GeneralChowIntersection.chowMap X m p q,
    General.GeneralChowIntersection.chowMap Y n p s,
    General.ChowPullback.pull P f m n p,
    ChowPushforwardMap.map f m n q s hdeg,
    ChowPushforwardMap.map f m n (p + q) (p + s) hdegCup,
    General.GeneralChowIntersection.chowIntersection_eq_singleton X m p q,
    General.GeneralChowIntersection.chowIntersection_eq_singleton Y n p s,
    General.ChowPullback.chowPullback_eq_singleton P f m n p,
    ChowPushforwardMap.graph f m n q s hdeg,
    ChowPushforwardMap.graph f m n (p + q) (p + s) hdegCup, ?_⟩
  exact General.Chow.Projection.chow P f m n p q s hdeg

end Construction

end

/-! The ProjectionFormula statement, with its proof supplied by the completed development. -/

open _root_.CategoryTheory

section

/-- ProjectionFormula: the projection formula, with explicit complementary degrees. -/
theorem projection_formula
    {X Y : TopCat.{0}}
    [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y]
    {m n : ℕ}
    (DX : Definitions.PoincareData X m) (DY : Definitions.PoincareData Y n)
    (f : X ⟶ Y)
    (p q s r t : ℕ)
    (hq : q + r = m)
    (hs : s + r = n)
    (hpq : (p + q) + t = m)
    (hps : (p + s) + t = n)
    (α : Definitions.HQ Y p) (β : Definitions.HQ X q) :
    Definitions.pushforward DX DY f (p + q) (p + s) t hpq hps
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) X p q
          (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f p α)
          β) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) Y p s α
        (Definitions.pushforward DX DY f q s r hq hs β) := by
  exact Construction.projection_formula DX DY f p q s r t hq hs hpq hps α β
end

open _root_.AlgebraicGeometry

/-- ProjectionFormula on Chow groups, including totality, descent, and independence of the
geometric representatives. Singleton equalities identify every output of each
relation, so the projection formula is neither conditional nor vacuous. -/
theorem chow_projection_formula
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (P : ProperCycleLinearity.ProductPresentation X Y)
    (m n : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap]
    (p q s : ℕ)
    (hdeg : q + n = s + m)
    (hdegCup : (p + q) + n = (p + s) + m) :
    ∃ (intersectionX : ProperCycleLinearity.ChowQ X p →ₗ[ℚ]
          ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (p + q))
      (intersectionY : ProperCycleLinearity.ChowQ Y p →ₗ[ℚ]
          ProperCycleLinearity.ChowQ Y s →ₗ[ℚ] ProperCycleLinearity.ChowQ Y (p + s))
      (pull : ProperCycleLinearity.ChowQ Y p →ₗ[ℚ] ProperCycleLinearity.ChowQ X p)
      (pushQ : ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ Y s)
      (pushPQ : ProperCycleLinearity.ChowQ X (p + q) →ₗ[ℚ]
          ProperCycleLinearity.ChowQ Y (p + s)),
      (∀ a b, Definitions.chowIntersection X p q a b = {intersectionX a b}) ∧
      (∀ a b, Definitions.chowIntersection Y p s a b = {intersectionY a b}) ∧
      (∀ a, Definitions.chowPullback P f n p a = {pull a}) ∧
      (∀ b, Definitions.chowPushforward f q s b = {pushQ b}) ∧
      (∀ c, Definitions.chowPushforward f (p + q) (p + s) c = {pushPQ c}) ∧
      ∀ (α : ProperCycleLinearity.ChowQ Y p) (β : ProperCycleLinearity.ChowQ X q),
        pushPQ (intersectionX (pull α) β) = intersectionY α (pushQ β) := by
  exact Construction.chow_projection_formula f hf P m n p q s hdeg hdegCup

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Chow
