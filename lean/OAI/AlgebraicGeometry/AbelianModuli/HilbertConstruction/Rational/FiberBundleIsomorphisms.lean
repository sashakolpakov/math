import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FiberFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointLineBundleTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.Support

/-! # Fiber Bundle Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Bundle isomorphisms on an abelian variety are determined by their fiber at the identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

theorem Line.Bundles.LineBundle.rationalFiber_iso_injective (p : X ⟶ Spec (.of K))
    [UniversallyClosed p] [IsReduced X] [ConnectedSpace X]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _) (L M : Line.Bundles.LineBundle X)
    (a b : L.sheaf ≅ M.sheaf)
    (h : (Scheme.Modules.pullback x).map a.hom = (Scheme.Modules.pullback x).map b.hom) : a = b :=
  Line.Bundles.LineBundle.iso_eq_of_pullback_eq p x hx L M (L.pullback x).trivialization_of_subsingleton.symm a b h

theorem Abelian.Schemes.AbelianScheme.lineBundleIso_ext_at_zero {g : ℕ} (A : Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (L M : Line.Bundles.LineBundle A.scheme.left) (a b : L.sheaf ≅ M.sheaf)
    (h : (Scheme.Modules.pullback η[A.scheme].left).map a.hom =
      (Scheme.Modules.pullback η[A.scheme].left).map b.hom) : a = b := by
  have : IsReduced A.scheme.left := A.reduced_overField
  have : ConnectedSpace A.scheme.left := A.connected_overField
  exact Line.Bundles.LineBundle.rationalFiber_iso_injective A.scheme.hom η[A.scheme].left η[A.scheme].w L M a b h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
