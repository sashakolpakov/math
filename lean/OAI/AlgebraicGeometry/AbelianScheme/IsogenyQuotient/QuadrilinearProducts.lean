import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorAssociativitySections
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairBilinearMaps

/-! # Quadrilinear Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearProducts.Construction

noncomputable section

/-! Four-input sheaf maps encode the two actual products in a
biextension interchange square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

structure SheafQuadrilinearMap (M N P Q R : X.Modules) where
  app (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)]
    Γ(P, U) →ₗ[Γ(X, U)] Γ(Q, U) →ₗ[Γ(X, U)] Γ(R, U)
  naturality {U V : X.Opens} (h : V ⟶ U) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) (q : Γ(Q, U)) :
    R.presheaf.map h.op (app U m n p q) =
      app V (M.presheaf.map h.op m) (N.presheaf.map h.op n) (P.presheaf.map h.op p) (Q.presheaf.map h.op q)

variable {M N P Q MN PQ R : X.Modules}

@[ext]
theorem SheafQuadrilinearMap.ext {b c : SheafQuadrilinearMap M N P Q R}
    (h : ∀ U, b.app U = c.app U) : b = c := by
  cases b
  cases c
  congr
  exact funext h

def SheafQuadrilinearMap.swapMiddle (b : SheafQuadrilinearMap M N P Q R) :
    SheafQuadrilinearMap M P N Q R where
  app U := LinearMap.lflip.toLinearMap.comp (b.app U)
  naturality h m p n q := b.naturality h m n p q

theorem SheafQuadrilinearMap.swapMiddle_app (b : SheafQuadrilinearMap M N P Q R)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) (q : Γ(Q, U)) :
    b.swapMiddle.app U m p n q = b.app U m n p q := rfl

theorem SheafQuadrilinearMap.swapMiddle_swapMiddle (b : SheafQuadrilinearMap M N P Q R) :
    b.swapMiddle.swapMiddle = b := by
  ext U m n p q
  rfl

def linePairBilinearCompose (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap P Q PQ)
    (d : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN PQ R) : SheafQuadrilinearMap M N P Q R where
  app U := PairBilinearMaps.Construction.pairBilinearLinearMap (b.app U) (c.app U) (d.app U)
  naturality h m n p q := by
    change R.presheaf.map h.op (d.app _ (b.app _ m n) (c.app _ p q)) = _
    rw [d.naturality, b.naturality, c.naturality]
    rfl

theorem linePairBilinearCompose_app (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N MN) (c : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap P Q PQ)
    (d : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap MN PQ R)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) (q : Γ(Q, U)) :
    (linePairBilinearCompose b c d).app U m n p q = d.app U (b.app U m n) (c.app U p q) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearProducts.Construction
