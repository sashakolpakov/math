import OAI.AlgebraicGeometry.PELModuli.CMPoints.PrimeToDegreeTorsion
import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFiberCount
import OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianProducts

/-! # Ordinary Isogeny -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryIsogeny

noncomputable section

/-! Ordinary geometric point counts are preserved by the constructed
prime-to-degree torsion isomorphisms and by actual abelian products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem torsion_card_eq_of_scalar_inverse {S : Scheme.{0}} {g : ℕ}
    (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : A.scheme ⟶ B.scheme) (h : B.scheme ⟶ A.scheme)
    [IsMonHom f] [IsMonHom h] (N d : ℕ) (hcop : N.Coprime d)
    (hgf : f ≫ h = A.multiplication d) (hfg : h ≫ f = B.multiplication d) (T : Over S) :
    Nat.card (A.torsionPoints N T) = Nat.card (B.torsionPoints N T) :=
  Nat.card_congr (((PrimeToDegreeTorsion.torsionIso_of_scalar_inverse A B f h N d hcop hgf hfg).app (.op T)).groupIsoToMulEquiv.toEquiv)

theorem ordinaryAt_iff_of_scalar_inverse {S : Scheme.{0}} {g q d : ℕ}
    (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : A.scheme ⟶ B.scheme) (h : B.scheme ⟶ A.scheme)
    [IsMonHom f] [IsMonHom h] (hcop : q.Coprime d)
    (hgf : f ≫ h = A.multiplication d) (hfg : h ≫ f = B.multiplication d) (x : S) :
    Models.IsOrdinaryAt q A.scheme x ↔ Models.IsOrdinaryAt q B.scheme x := by
  have hdim : topologicalKrullDim (A.scheme.hom.fiber x) = topologicalKrullDim (B.scheme.hom.fiber x) :=
    (OrdinaryFiberCount.abelian_fiber_dimension A x).trans (OrdinaryFiberCount.abelian_fiber_dimension B x).symm
  have hc := torsion_card_eq_of_scalar_inverse A B f h q d hcop hgf hfg (Models.geometricPoint S x)
  change (∃ n : ℕ, _ = (n : WithBot ℕ∞) ∧ Nat.card (A.torsionPoints q (Models.geometricPoint S x)) = q ^ n) ↔
    (∃ n : ℕ, _ = (n : WithBot ℕ∞) ∧ Nat.card (B.torsionPoints q (Models.geometricPoint S x)) = q ^ n)
  rw [hdim, hc]

theorem abelianProduct_torsion_card {S : Scheme.{0}} {g h : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S) (N : ℕ) (T : Over S) :
    Nat.card ((AbelianProducts.abelianProduct A B).torsionPoints N T) =
      Nat.card (A.torsionPoints N T) * Nat.card (B.torsionPoints N T) :=
  (Nat.card_congr (AbelianProducts.abelianProductTorsionEquiv A B N T).toEquiv).trans (Nat.card_prod _ _)

theorem abelianProduct_ordinary_count {S : Scheme.{0}} {g h q : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S) (T : Over S)
    (hA : Nat.card (A.torsionPoints q T) = q ^ g)
    (hB : Nat.card (B.torsionPoints q T) = q ^ h) :
    Nat.card ((AbelianProducts.abelianProduct A B).torsionPoints q T) = q ^ (g + h) := by
  rw [abelianProduct_torsion_card, hA, hB, pow_add]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryIsogeny
