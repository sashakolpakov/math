import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange

/-! # Index Equivalence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.IndexEquivalence.CechIndexEquivalence

noncomputable section

/-! The original Cech complex is unchanged by an equivalence of index types,
including index types in different universes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v a b w z
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type a} [Category.{b} A] [HasProducts.{w} A] [HasProducts.{z} A]
  {ι : Type w} {κ : Type z} (e : κ ≃ ι) (U : ι → C) (P : Cᵒᵖ ⥤ A)

abbrev tuples (n : ℕ) : (Fin (n + 1) → κ) ≃ (Fin (n + 1) → ι) :=
  Equiv.piCongrRight (fun _ => e)

abbrev coefficients (n : ℕ) (t : Fin (n + 1) → ι) : A := P.obj (op (∏ᶜ (U ∘ t)))

def tupleMap {n m : SimplexCategory} (α : n ⟶ m) (t : Fin (m.len + 1) → ι) :
    coefficients U P n.len (t ∘ α.toOrderHom) ⟶ coefficients U P m.len t :=
  P.map (Pi.lift (fun i => Pi.π (U ∘ t) (α.toOrderHom i))).op

omit [HasProducts.{z} A] in
theorem map_eq {n m : SimplexCategory} (α : n ⟶ m) :
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P).map α =
      Pi.lift (fun t => Pi.π (coefficients U P n.len) (t ∘ α.toOrderHom) ≫ tupleMap U P α t) := rfl

def component (n : SimplexCategory) :
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk κ (U ∘ e)).cech).obj P).obj n ≅
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P).obj n :=
  Pi.reindex (tuples e n.len) (fun t => P.obj (op (∏ᶜ (U ∘ t))))

theorem naturality {n m : SimplexCategory} (α : n ⟶ m) :
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk κ (U ∘ e)).cech).obj P).map α ≫
      (component e U P m).hom =
    (component e U P n).hom ≫
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P).map α := by
  change Pi.lift (f := coefficients U P m.len ∘ tuples e m.len)
    (fun t => Pi.π (coefficients U P n.len ∘ tuples e n.len) (t ∘ α.toOrderHom) ≫
      tupleMap (U ∘ e) P α t) ≫ (Pi.reindex (tuples e m.len) (coefficients U P m.len)).hom =
    (Pi.reindex (tuples e n.len) (coefficients U P n.len)).hom ≫
      Pi.lift (f := coefficients U P m.len)
        (fun t => Pi.π (coefficients U P n.len) (t ∘ α.toOrderHom) ≫ tupleMap U P α t)
  apply Pi.hom_ext
  intro t
  obtain ⟨s, rfl⟩ := (tuples e m.len).surjective t
  simp only [Category.assoc, Pi.reindex_hom_π, Pi.lift_comp_π]
  exact (Pi.reindex_hom_π_assoc (tuples e n.len) (coefficients U P n.len)
    (s ∘ α.toOrderHom) (tupleMap (U ∘ e) P α s)).symm

def cosimplicialIso :
    (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk κ (U ∘ e)).cech).obj P ≅
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P :=
  NatIso.ofComponents (component e U P) (fun α => naturality e U P α)

def complexIso [Preadditive A] : (cechComplexFunctor (U ∘ e)).obj P ≅ (cechComplexFunctor U).obj P :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).mapIso (cosimplicialIso e U P)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.IndexEquivalence.CechIndexEquivalence
