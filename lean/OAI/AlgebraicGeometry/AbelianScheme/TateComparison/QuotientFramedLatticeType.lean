import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedLatticeQuotients
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientCokernelType

/-! # Quotient Framed Lattice Type -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.QuotientFramedLatticeType.SphericalPELAlbaneseData

noncomputable section

/-! IsogenyQuotient's actual isogeny gives the prescribed finite quotient of the
projected lattices in any compatible source frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) (h : D.RealizesIsogenyQuotient)
  {k : Type} [Field k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} (t : Local.IntegralType s)
  (x y : D.GeometricPoint b) (c : Over.mk b ⟶ (D.correspondence t).cover)
  (hs : c ≫ (D.correspondence t).source = x) (ht : c ≫ (D.correspondence t).target = y)
  (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)
  (v : Fin s)

local instance : Module ℤ_[q]
    (Add.schemeTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :=
  inferInstanceAs (Module ℤ_[q]
    (Add.Tate.compatible (H := Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ (D.fiberFamily b x).abelian.scheme)) q))

local instance : Module ℚ_[q]
    (Rational.rationalTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :=
  TensorProduct.leftModule

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.c46FiberFramedLatticeQuotientType :
    D.framedTateLatticeQuotient
      (P := D.fiberFamily b x) (Q := D.fiberFamily b y) (m := t.multiplierNat)
      (D.c46FiberIsogeny h t x y c hs ht) frame (v, false) ≃+
      (∀ i : Fin 3, ZMod (q ^ t.exponentNat v i)) :=
  (D.tateBlockCokernelEquivFramedQuotient hg
    (P := D.fiberFamily b x) (Q := D.fiberFamily b y) (m := t.multiplierNat) (D.c46FiberIsogeny h t x y c hs ht) frame hf
    D.reference.polarizationType (D.fiberPolarizationType hgeometry b x) hg.2.2.2.2
    (v, false)).symm.toAddEquiv.trans
      (D.c46FiberTateBlockCokernelType hg hgeometry h t x y c hs ht v)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.QuotientFramedLatticeType.SphericalPELAlbaneseData
