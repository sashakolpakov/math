import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.ProductLift

/-! # Hom Products -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.HomProducts.CrystallinePrincipalHomProducts

noncomputable section

/-!
# Arrows into native principal intersections

Arrows into an intersection are equivalent to a base arrow together with
compatible arrows into all factors. The compatibility is expressed in
the original native crystalline category. The product lift supplies the
inverse; monicity of principal projections gives uniqueness.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q T : Site.Object p k X)

def OverHom (q : T ⟶ Q) (r : PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring) :=
  { f : T ⟶ Functor.CrystallinePrincipalFunctor.object p k X Q r //
    f ≫ Functor.CrystallinePrincipalFunctor.projection p k X Q r = q }

instance overHom_subsingleton (q : T ⟶ Q)
    (r : PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring) :
    Subsingleton (OverHom p k X Q T q r) := by
  refine ⟨fun f g => Subtype.ext ?_⟩
  exact (cancel_mono (Functor.CrystallinePrincipalFunctor.projection p k X Q r)).mp
    (f.property.trans g.property.symm)

def overEquiv (r : PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring) :
    (T ⟶ Functor.CrystallinePrincipalFunctor.object p k X Q r) ≃
      Σ q : T ⟶ Q, OverHom p k X Q T q r where
  toFun f := ⟨f ≫ Functor.CrystallinePrincipalFunctor.projection p k X Q r, ⟨f, rfl⟩⟩
  invFun f := f.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨q, f, hf⟩
    cases hf
    rfl

variable {α : Type v} [Fintype α]
  (r : α → PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring)

def productEquiv (q : T ⟶ Q) : OverHom p k X Q T q (∏ᶜ r) ≃
    ∀ i, OverHom p k X Q T q (r i) where
  toFun f i := ⟨f.val ≫ Functor.CrystallinePrincipalFunctor.map p k X Q (Pi.π r i),
    (Category.assoc _ _ _).trans
      ((congrArg (fun a => f.val ≫ a)
        (Functor.CrystallinePrincipalFunctor.map_projection p k X Q (Pi.π r i))).trans f.property)⟩
  invFun f :=
    ⟨(ProductLift.CrystallinePrincipalProductLift.lift p k X Q r (Over.mk q)
      (fun i => Over.homMk (f i).val (f i).property)).left, Over.w _⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

def homProductEquiv : (T ⟶ Functor.CrystallinePrincipalFunctor.object p k X Q (∏ᶜ r)) ≃
    Σ q : T ⟶ Q, ∀ i, OverHom p k X Q T q (r i) :=
  (overEquiv p k X Q T (∏ᶜ r)).trans
    (Equiv.sigmaCongrRight (fun q => productEquiv p k X Q T r q))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.HomProducts.CrystallinePrincipalHomProducts
