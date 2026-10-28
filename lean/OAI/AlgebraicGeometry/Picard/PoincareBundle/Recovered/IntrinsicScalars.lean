import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentComponentIsomorphisms
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedRecovery

/-! # Intrinsic Scalars -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.IntrinsicScalars.Intrinsic

noncomputable section

/-! Full ordinary recovery identifies actual native gluing scalars in the recovered global frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
  (r : Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks) (f := fun (_ : PUnit.{1}) => f) M ≅ D)
  (e : D.obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

/-- Recovery transports the original global frame to the actual pulled quotient line. -/
def frame : (Scheme.Modules.pullback f).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  DescentComponentIsomorphisms.componentIso Geometric.KernelLinearization.modulePullbacks f r ≪≫ e

/-- The full actual scalar is preserved by the recovered descent isomorphism. -/
theorem scalar_eq {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M) (frame f M D r e) q x y hx hy =
      Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D) e q x y hx hy :=
  AbelianScheme.CartierDuality.FramedRecovery.Construction.LineDescent.framedDescentScalar_eq_of_recovery (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M)
    (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D)
    (DescentComponentIsomorphisms.componentIso Geometric.KernelLinearization.modulePullbacks f r) e q x y hx hy
    (r.hom.comm q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.IntrinsicScalars.Intrinsic
