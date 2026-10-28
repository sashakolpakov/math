import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.DescentIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.PullbackLineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.CanonicalCompatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.DescentIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.KernelPairCompatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.SquareDescent

/-! # Line Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.LineRecovery

noncomputable section

/-! A compatible actual pulled-line isomorphism supplies full recovery in the descent category. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B) (L : Line.Bundles.LineBundle B.left)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f.left))
  (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ D.obj PUnit.unit)

variable
    (h : ∀ (T : Over S) (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x.left).map e.hom ≫
        (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f.left D).hom q.left x.left y.left
          (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
      (Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum f (Line.Comparison.Bundle.toShared L)).hom q.left x.left y.left
        (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫
          (Scheme.Modules.pullback y.left).map e.hom)

include h in
/-- The canonical native formula supplies the entire ordinary compatibility family. -/
theorem ordinary_compatibility (T : Over S) (q : T ⟶ B) (x y : T ⟶ A)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Scheme.Modules.pullback x.left).map e.hom ≫ D.hom q.left
      (i₁ := PUnit.unit) (i₂ := PUnit.unit) x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks) (f := fun (_ : PUnit.{1}) => f.left) L.sheaf).hom
      q.left (i₁ := PUnit.unit) (i₂ := PUnit.unit) x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫
        (Scheme.Modules.pullback y.left).map e.hom :=
  CanonicalCompatibility.compatibility f L D e q x y hx hy (h T q x y hx hy)

/-- Native canonical gluing compatibility constructs the actual recovered line isomorphism. -/
def iso :
    Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks) (f := fun (_ : PUnit.{1}) => f.left) L.sheaf ≅ D :=
  Recovered.SquareDescent.originalIso f.left D L.sheaf e (by
    have he := Ordinary.KernelPairCompatibility.compatibility f
      (Recovered.OrdinaryDatum.Ordinary.baseDatum f.left L.sheaf) D e (ordinary_compatibility f L D e h)
    rw [Recovered.OrdinaryDatum.Ordinary.baseDatum_gluing] at he
    exact he)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.LineRecovery
