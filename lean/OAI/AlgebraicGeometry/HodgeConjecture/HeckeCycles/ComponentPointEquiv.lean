import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DisjointPointCover
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection

/-! # Component Point Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComponentPointEquiv.CM

noncomputable section

/-! The original component decomposition gives a bijection between
component-labelled ordinary points and ordinary points of the full
geometric source. The ordinary predicates are the same pulled-back locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM

def sigmaSubtype {I : Type} {A : I → Type} (P : (Σ i, A i) → Prop) :
    (Σ i, {x : A i // P ⟨i, x⟩}) ≃ {x : Σ i, A i // P x} where
  toFun x := ⟨⟨x.1, x.2.val⟩, x.2.property⟩
  invFun x := ⟨x.val.1, ⟨x.val.2, x.property⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j) (a : M.Family)

local instance component_open (i : Fin (M.componentCount a)) :
    IsOpenImmersion (Ordinary.Locus.CM.componentFiberInclusion R a i).left := Ordinary.Locus.CM.componentFiberInclusion_open R a i

def pointEquiv :
    (Σ i : Fin (M.componentCount a), Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ Ordinary.Locus.CM.componentFiber R a i) ≃
      (Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a) :=
  DisjointPointCover.CM.pointEquiv (Ordinary.Locus.CM.componentFiber R a) (Ordinary.Locus.CM.componentFiberInclusion R a)
    (PELModuli.IntegralModel.Coproduct.baseChange_decomposition_cover (M.components a).S R.geometricBase (M.decomposition a))
    (PELModuli.IntegralModel.Coproduct.baseChange_decomposition_disjoint (M.components a).S R.geometricBase (M.decomposition a))
    (𝟙 _)

def ordinaryEquiv : Intrinsic.Detection.CM.ordinaryPoints R a ≃
    {p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a //
      R.IsOrdinary a (p.left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q))))} := by
  let P (x : Σ i : Fin (M.componentCount a),
      Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ Ordinary.Locus.CM.componentFiber R a i) : Prop :=
    x.2.left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q))) ∈ Ordinary.Locus.CM.componentOrdinaryLocus R a x.1
  let Q (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a) : Prop :=
    R.IsOrdinary a (p.left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q))))
  have h : ∀ x, P x ↔ Q (pointEquiv R a x) := fun _ => Iff.rfl
  exact (sigmaSubtype P).trans ((pointEquiv R a).subtypeEquiv h)

theorem ordinaryEquiv_val (x : Intrinsic.Detection.CM.ordinaryPoints R a) :
    (ordinaryEquiv R a x).val = x.2.val ≫ Ordinary.Locus.CM.componentFiberInclusion R a x.1 := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComponentPointEquiv.CM
