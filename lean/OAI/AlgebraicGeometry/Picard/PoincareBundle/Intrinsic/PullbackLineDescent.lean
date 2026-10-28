import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.DescentReindex
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison

/-! # Pullback Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.PullbackLineDescent

noncomputable section

/-! Canonical native descent of an actual pulled line is the composition of its two geometric fiber comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v w₁ w₂

open OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCocycle.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

/-- Canonical pseudofunctor gluing factors through the common quotient fiber. -/
theorem canonical_hom {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w₁, w₂}) {A B : C}
    (f : A ⟶ B) (M : F.obj (.mk (op B))) {T : C}
    (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Pseudofunctor.DescentData.ofObj (F := F) (f := fun (_ : PUnit.{1}) => f) M).hom
      q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      (PullbackFiberComposition.fiberIsoTo F f M x q hx).hom ≫
        (PullbackFiberComposition.fiberIsoTo F f M y q hy).inv := rfl

/-- On schemes, the pseudofunctor comparison is the native pullback composition isomorphism. -/
theorem scheme_comparison {X Y T : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (x : T ⟶ X) (q : T ⟶ Y) (hx : x ≫ f = q) :
    PullbackFiberComposition.fiberIsoTo Geometric.KernelLinearization.modulePullbacks f M x q hx =
      (Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).app M := by
  subst q
  apply Iso.ext
  rfl

variable {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B) (L : Line.Bundles.LineBundle B.left)

/-- The native wrapper retains the underlying canonical pseudofunctor gluing map. -/
theorem native_hom {T : Over S} (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum f (Line.Comparison.Bundle.toShared L)).hom q.left x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks) (f := fun (_ : PUnit.{1}) => f.left) L.sheaf).hom
      q.left (i₁ := PUnit.unit) (i₂ := PUnit.unit) x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) := rfl

/-- Over the original base, canonical gluing is the product of the two specified fiber comparisons. -/
theorem over_hom {T : Over S} (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.overModulePullbacks S) (f := fun (_ : PUnit.{1}) => f) L.sheaf).hom
      q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
    (GlobalPullbackFrame.comparison f L x q hx).hom ≫ (GlobalPullbackFrame.comparison f L y q hy).inv :=
  canonical_hom (Geometric.KernelLinearization.overModulePullbacks S) f L.sheaf q x y hx hy

/-- The native pullback-line gluing map is exactly the two actual composition comparisons. -/
theorem hom_eq {T : Over S} (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum f (Line.Comparison.Bundle.toShared L)).hom q.left x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (GlobalPullbackFrame.comparison f L x q hx).hom ≫ (GlobalPullbackFrame.comparison f L y q hy).inv := by
  refine (native_hom f L q x y hx hy).trans ?_
  have h := canonical_hom Geometric.KernelLinearization.modulePullbacks f.left L.sheaf q.left x.left y.left
    (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy)
  rw [scheme_comparison f.left L.sheaf x.left q.left (congrArg Over.Hom.left hx),
    scheme_comparison f.left L.sheaf y.left q.left (congrArg Over.Hom.left hy)] at h
  rw [← GlobalPullbackFrame.comparison_eq f L x q hx, ← GlobalPullbackFrame.comparison_eq f L y q hy] at h
  exact h

/-- The same identity holds as an actual line-fiber isomorphism. -/
theorem iso_eq {T : Over S} (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum f (Line.Comparison.Bundle.toShared L)).iso q.left x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    GlobalPullbackFrame.comparison f L x q hx ≪≫ (GlobalPullbackFrame.comparison f L y q hy).symm := by
  apply Iso.ext
  exact hom_eq f L q x y hx hy

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.PullbackLineDescent
