import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.HomProducts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech

/-! # Arrow Tuples -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.ArrowTuples.CrystallineCechArrowTuples

noncomputable section

/-!
# Native Čech arrows as tuples of lifts of a base arrow

For a fixed test object, a simplex consists of a base arrow and an ordered
tuple of its lifts to cover members. The equivalence uses the actual
principal-intersection product and its native universal property.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u v

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q T : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring)

def LiftIndex (q : T ⟶ Q) :=
  Σ i : ι, CrystallinePrincipal.HomProducts.CrystallinePrincipalHomProducts.OverHom p k X Q T q (CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s i)

def reindex (α : Type v) :
    (Σ t : α → ι, Σ q : T ⟶ Q,
      ∀ l, CrystallinePrincipal.HomProducts.CrystallinePrincipalHomProducts.OverHom p k X Q T q (CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s (t l))) ≃
        Σ q : T ⟶ Q, α → LiftIndex p k X Q T s q where
  toFun z := ⟨z.2.1, fun l => ⟨z.1 l, z.2.2 l⟩⟩
  invFun z := ⟨fun l => (z.2 l).1, z.1, fun l => (z.2 l).2⟩
  left_inv := by rintro ⟨t, q, f⟩; rfl
  right_inv := by
    rintro ⟨q, f⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    funext l
    exact Sigma.eta (f l)

local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s))

def equiv (n : ℕ) :
    (Σ t : ((N).obj (op ⦋n⦌)).I,
      T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋n⦌)).obj t)) ≃
        Σ q : T ⟶ Q, Fin (n + 1) → LiftIndex p k X Q T s q :=
  (Equiv.sigmaCongrRight (fun t : Fin (n + 1) → ι =>
    CrystallinePrincipal.HomProducts.CrystallinePrincipalHomProducts.homProductEquiv p k X Q T
      (fun l : Fin (n + 1) => CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s (t l)))).trans
        (reindex p k X Q T s (Fin (n + 1)))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.ArrowTuples.CrystallineCechArrowTuples
