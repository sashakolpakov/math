import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.DescentOverTests

/-! # Descent Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.DescentIso

noncomputable section

/-! Actual native compatibility constructs an isomorphism in the ordinary descent category. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
  (D E : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f.left))
  (e : D.obj PUnit.unit ≅ E.obj PUnit.unit)

/-- Testing actual gluing over the original base constructs a full ordinary descent isomorphism. -/
def iso_of_over
    (h : ∀ (T : Over S) (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x.left).map e.hom ≫
        (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f.left E).hom q.left x.left y.left
          (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
      (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f.left D).hom q.left x.left y.left
        (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫
          (Scheme.Modules.pullback y.left).map e.hom) : D ≅ E :=
  Pseudofunctor.DescentData.isoMk (fun _ => e) (by
    intro T q i j x y hx hy
    cases i
    cases j
    exact DescentOverTests.hom_compatible f
      (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f.left D) (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f.left E)
      e h q x y hx hy)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.DescentIso
