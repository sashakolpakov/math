import OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleSplitting
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleTransport
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation

/-! # Group Cocycle Splitting -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.GroupCocycleSplitting

noncomputable section

/-! Split a regular cocycle on a finite commutative group scheme without supplied coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] (H : Over (Spec (.of k)))
  [GrpObj H] [IsCommMonObj H] [IsFinite H.hom]
  (C : NaturalSchemeCocycle.NaturalCocycle H)

/-- A natural regular splitting exists on the original group, including all infinitesimal tests. -/
theorem exists_splitting :
    ∃ v : ∀ T : Over (Spec (.of k)), (T ⟶ H) → Γ(T.left, ⊤)ˣ,
      (∀ T : Over (Spec (.of k)), v T 1 = 1) ∧
      (∀ {T U : Over (Spec (.of k))} (g : U ⟶ T) (a : T ⟶ H),
        Units.map g.left.appTop.hom (v T a) = v U (g ≫ a)) ∧
      ∀ (T : Over (Spec (.of k))) (a b : T ⟶ H),
        C.value a b * v T (a * b) = v T a * v T b := by
  obtain ⟨R, hf, hc, ⟨e⟩⟩ := Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k (Grp.mk H)
  have : Module.Finite k R := hf
  have : Coalgebra.IsCocomm k R := hc
  let i : ((Spec (.of R)).asOver (Spec (.of k))) ≅ H := (Grp.forget _).mapIso e
  have : IsMonHom i.hom := inferInstanceAs (IsMonHom e.hom.hom.hom)
  have : IsMonHom i.inv := inferInstanceAs (IsMonHom e.inv.hom.hom)
  let C' := SchemeCocycleTransport.pullback i.hom C
  obtain ⟨a, haone, hamul⟩ := SchemeCocycleSplitting.exists_regular_splitting k R C'
  let v (T : Over (Spec (.of k))) (x : T ⟶ H) :=
    CocycleSchemeValues.solution k R a T (x ≫ i.inv)
  refine ⟨v, ?_, ?_, ?_⟩
  · intro T
    change CocycleSchemeValues.solution k R a T ((1 : T ⟶ H) ≫ i.inv) = 1
    rw [MonObj.one_comp]
    exact haone T
  · intro T U g x
    exact (CocycleSchemeValues.solution_natural k R a g (x ≫ i.inv)).trans
      (congrArg (CocycleSchemeValues.solution k R a U) (Category.assoc g x i.inv).symm)
  · intro T x y
    have h := hamul T (x ≫ i.inv) (y ≫ i.inv)
    have hx : (x ≫ i.inv) ≫ i.hom = x := by simp only [Category.assoc, i.inv_hom_id, Category.comp_id]
    have hy : (y ≫ i.inv) ≫ i.hom = y := by simp only [Category.assoc, i.inv_hom_id, Category.comp_id]
    have hv : C'.value (x ≫ i.inv) (y ≫ i.inv) = C.value x y :=
      (SchemeCocycleTransport.value i.hom C (x ≫ i.inv) (y ≫ i.inv)).trans
        (congrArg₂ (fun p q : T ⟶ H => C.value p q) hx hy)
    have hp : (x * y) ≫ i.inv = (x ≫ i.inv) * (y ≫ i.inv) := MonObj.mul_comp x y i.inv
    exact (congrArg₂ (fun c z => c * CocycleSchemeValues.solution k R a T z) hv.symm hp).trans h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.GroupCocycleSplitting
