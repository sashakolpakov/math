import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.EquivarianceTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

/-! # Fiber Bilinear Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearGluing

noncomputable section

/-!
# Actual line-fiber equivariance gives gluing of pulled-back bilinear sheaf maps
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {S : Scheme.{u}} {E K T : Over S} (L : Line.Bundles.LineBundle E.left)
  (p q : T ⟶ K)

/-- Translate a genuine map between original line fibers into the two iterated pullback presentations. -/
def fiberTransport (i : K ⟶ E) (σ : Line.Fibers.fiber L (p ≫ i) ⟶ Line.Fibers.fiber L (q ≫ i)) :
    (Scheme.Modules.pullback p.left).obj (Line.Fibers.fiber L i) ⟶ (Scheme.Modules.pullback q.left).obj (Line.Fibers.fiber L i) :=
  (Line.Fibers.fiberPullbackIso L p i (p ≫ i) rfl).hom ≫ σ ≫ (Line.Fibers.fiberPullbackIso L q i (q ≫ i) rfl).inv

/-- On composite points the fiber transport uses precisely the geometric composition maps. -/
theorem fiberTransport_eq_comp (i : K ⟶ E) (σ : Line.Fibers.fiber L (p ≫ i) ⟶ Line.Fibers.fiber L (q ≫ i)) :
    fiberTransport L p q i σ =
      (Scheme.Modules.pullbackComp p.left i.left).hom.app L.sheaf ≫ σ ≫
        (Scheme.Modules.pullbackComp q.left i.left).inv.app L.sheaf := by
  simp only [fiberTransport, Line.Fibers.fiberPullbackIso, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl]
  rfl

variable (i j k : K ⟶ E) (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L i) (Line.Fibers.fiber L j) (Line.Fibers.fiber L k))
  (σi : Line.Fibers.fiber L (p ≫ i) ⟶ Line.Fibers.fiber L (q ≫ i))
  (σj : Line.Fibers.fiber L (p ≫ j) ⟶ Line.Fibers.fiber L (q ≫ j))
  (σk : Line.Fibers.fiber L (p ≫ k) ⟶ Line.Fibers.fiber L (q ≫ k))

/-- Fiberwise equivariance yields the full bilinear gluing equation in the raw geometric pullback sheaves. -/
theorem equivariance_of_fibers
    (h : (Line.Fibers.pullBilinear L q i j k (q ≫ i) (q ≫ j) (q ≫ k) rfl rfl rfl β).precomp σi σj =
      (Line.Fibers.pullBilinear L p i j k (p ≫ i) (p ≫ j) (p ≫ k) rfl rfl rfl β).postcomp σk) :
    (Bilinear.BilinearPullback.pullback q.left (Line.Fibers.fiber_isLine L i) (Line.Fibers.fiber_isLine L j) β).precomp
      (fiberTransport L p q i σi) (fiberTransport L p q j σj) =
    (Bilinear.BilinearPullback.pullback p.left (Line.Fibers.fiber_isLine L i) (Line.Fibers.fiber_isLine L j) β).postcomp
      (fiberTransport L p q k σk) :=
  Bilinear.EquivarianceTransport.of_transport
    (Bilinear.BilinearPullback.pullback p.left (Line.Fibers.fiber_isLine L i) (Line.Fibers.fiber_isLine L j) β)
    (Bilinear.BilinearPullback.pullback q.left (Line.Fibers.fiber_isLine L i) (Line.Fibers.fiber_isLine L j) β)
    (Line.Fibers.fiberPullbackIso L p i (p ≫ i) rfl) (Line.Fibers.fiberPullbackIso L p j (p ≫ j) rfl)
    (Line.Fibers.fiberPullbackIso L p k (p ≫ k) rfl) (Line.Fibers.fiberPullbackIso L q i (q ≫ i) rfl)
    (Line.Fibers.fiberPullbackIso L q j (q ≫ j) rfl) (Line.Fibers.fiberPullbackIso L q k (q ≫ k) rfl) σi σj σk h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearGluing
