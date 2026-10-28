import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFromFactors
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts

/-! # Ordinary Fiber Count -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFiberCount

noncomputable section

/-! The point count on the actual geometric fiber is equivalent to
the ordinary predicate used in Openness and the repaired CMPoints statement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem abelian_fiber_dimension {S : Scheme.{0}} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (x : S) :
    topologicalKrullDim (A.scheme.hom.fiber x) = (g : WithBot ℕ∞) := by
  let : IsOpenImmersion (Over.Hom.left (𝟙 A.scheme)) := inferInstanceAs (IsOpenImmersion (𝟙 A.scheme.left))
  apply ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts.Construction.dimension_fiber_of_smooth_chart A.scheme A.scheme (𝟙 _) g x
  refine ⟨η[A.scheme].left x, ?_⟩
  have h : η[A.scheme].left ≫ A.scheme.hom = 𝟙 S := (η[A.scheme]).w
  exact (Scheme.Hom.comp_apply _ _ x).symm.trans (congrArg (fun f : S ⟶ S => f x) h)

def geometricTorsionPointsEquiv {S : Scheme.{0}} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (x : S) (m : ℕ) :
    (A.pullback (Models.geometricPoint S x).hom).torsionPoints m
      (Over.mk (𝟙 (Spec (.of (AlgebraicClosure (S.residueField x)))))) ≃
      {z : Models.geometricPoint S x ⟶ A.scheme // z ^ m = 1} := by
  let p := (Models.geometricPoint S x).hom
  let T : Over (Spec (.of (AlgebraicClosure (S.residueField x)))) := Over.mk (𝟙 _)
  let e : (Over.map p).obj T ≅ Models.geometricPoint S x := Over.isoMk (Iso.refl _) (by rfl)
  exact (A.torsionBaseChangeEquiv p T m).toEquiv.trans
    (Equiv.ofBijective (((A.torsionFunctor m).mapIso e.op).hom)
      (ConcreteCategory.bijective_of_isIso _))

theorem isOrdinaryAt_iff_geometricFiber_count {S : Scheme.{0}} {g q : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (x : S) :
    Models.IsOrdinaryAt q A.scheme x ↔
      Nat.card ((A.pullback (Models.geometricPoint S x).hom).torsionPoints q
        (Over.mk (𝟙 (Spec (.of (AlgebraicClosure (S.residueField x))))))) = q ^ g := by
  have hc := Nat.card_congr (geometricTorsionPointsEquiv A x q)
  constructor
  · rintro ⟨d, hd, hn⟩
    have hdg : d = g := by
      exact_mod_cast hd.symm.trans (abelian_fiber_dimension A x)
    subst d
    exact hc.trans hn
  · intro h
    exact ⟨g, abelian_fiber_dimension A x, hc.symm.trans h⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFiberCount
