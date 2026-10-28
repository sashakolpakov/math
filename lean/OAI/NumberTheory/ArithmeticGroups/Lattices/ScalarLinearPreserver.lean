import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Quotient

/-! # Scalar Linear Preserver -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ScalarLinearPreserver.Construction

noncomputable section

/-! A real linear automorphism commuting with the coefficient algebra
lifts uniquely to an automorphism linear over that algebra. -/

open scoped Classical

def scalarLinearEquivOfCommutes
    {R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module S V] [Module R V] [IsScalarTower R S V]
    (f : V ≃ₗ[R] V) (hf : ∀ (a : S) (x : V), f (a • x) = a • f x) : V ≃ₗ[S] V where
  toFun := f
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv
  map_add' := f.map_add
  map_smul' := hf

theorem scalarLinearEquivOfCommutes_restrictScalars
    {R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module S V] [Module R V] [IsScalarTower R S V]
    (f : V ≃ₗ[R] V) (hf : ∀ (a : S) (x : V), f (a • x) = a • f x) :
    (scalarLinearEquivOfCommutes f hf).restrictScalars R = f := by
  ext x
  rfl

theorem commutes_scalar_of_basis
    {R S V I : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module S V] [Module R V] [IsScalarTower R S V]
    (b : Module.Basis I R S) (f : V →ₗ[R] V)
    (hf : ∀ i x, f (b i • x) = b i • f x) :
    ∀ (a : S) (x : V), f (a • x) = a • f x := by
  intro a x
  have hspan : ∀ a ∈ Submodule.span R (Set.range b), f (a • x) = a • f x := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha => obtain ⟨i, rfl⟩ := ha; exact hf i x
    | zero => simp
    | add a c _ _ ha hc => simp only [add_smul, map_add, ha, hc]
    | smul c a _ ha =>
        rw [smul_assoc, map_smul, ha, smul_assoc]
  exact hspan a (b.span_eq.symm ▸ Submodule.mem_top)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ScalarLinearPreserver.Construction
