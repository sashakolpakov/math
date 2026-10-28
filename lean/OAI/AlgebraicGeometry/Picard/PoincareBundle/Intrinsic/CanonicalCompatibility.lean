import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.PullbackLineDescent

/-! # Canonical Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.CanonicalCompatibility

noncomputable section

/-! The explicit canonical gluing formula transfers compatibility into the ordinary descent interface. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B) (L : Line.Bundles.LineBundle B.left)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f.left))
  (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ D.obj PUnit.unit)

/-- The actual native pullback-line morphism is precisely the ordinary canonical gluing map. -/
theorem compatibility {T : Over S} (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (h : (Scheme.Modules.pullback x.left).map e.hom ≫
      (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f.left D).hom q.left x.left y.left
        (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
      (Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum f (Line.Comparison.Bundle.toShared L)).hom q.left x.left y.left
        (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫
          (Scheme.Modules.pullback y.left).map e.hom) :
    (Scheme.Modules.pullback x.left).map e.hom ≫
      D.hom q.left (i₁ := PUnit.unit) (i₂ := PUnit.unit) x.left y.left
        (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
      (Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks) (f := fun (_ : PUnit.{1}) => f.left) L.sheaf).hom
        q.left (i₁ := PUnit.unit) (i₂ := PUnit.unit) x.left y.left
          (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫
            (Scheme.Modules.pullback y.left).map e.hom := by
  exact h.trans (congrArg (fun v => v ≫ (Scheme.Modules.pullback y.left).map e.hom)
    (PullbackLineDescent.native_hom f L q x y hx hy))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.CanonicalCompatibility
