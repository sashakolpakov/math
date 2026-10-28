import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsogenyComplement
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Product

/-! # Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Action.Construction

noncomputable section

/-!
Descent of the integral action through the constructed quotient. The
ring identities are proved by epimorphic cancellation. Stability follows
from the scalar action on split torsion blocks and closure of a subgroup
under integer powers; no descended action is an input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v w

section Action

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {A B H : C} [GrpObj A] [GrpObj B]
variable (R : Type w) [Ring R]

/-- A ring action by actual group-object endomorphisms. The group law
is written multiplicatively, so the zero endomorphism is `1`. -/
@[ext] structure EndomorphismAction where
  map : R → (A ⟶ A)
  preservesGroup : ∀ r, IsMonHom (map r)
  map_zero : map 0 = 1
  map_one : map 1 = 𝟙 A
  map_add : ∀ r t, map (r + t) = map r * map t
  map_mul : ∀ r t, map (r * t) = map t ≫ map r

attribute [instance] EndomorphismAction.preservesGroup

variable {R}

/-- Construct the unique ring action on a quotient whose kernel is stable.
The hypotheses on the quotient are exactly FiniteDescent's universal property plus
the product epimorphism supplied by its finite flat surjectivity. -/
theorem quotient_ring_action
    (ρ : EndomorphismAction (A := A) R)
    (i : H ⟶ A) (f : A ⟶ B) [IsMonHom f] [Epi (f ⊗ₘ f)]
    (hkernel : i ≫ f = 1) (h_FiniteDescent : Descent.Construction.QuotientUniversalProperty i f)
    (hstable : ∀ r, i ≫ ρ.map r ≫ f = 1) :
    ∃! σ : EndomorphismAction (A := B) R,
      ∀ r, f ≫ σ.map r = ρ.map r ≫ f := by
  have hex r := Descent.Construction.endomorphism_descent_of_FiniteDescent i f h_FiniteDescent (ρ.map r) (hstable r)
  let d := fun r => Classical.choose (hex r)
  have hd r : f ≫ d r = ρ.map r ≫ f := (Classical.choose_spec (hex r)).1
  have : Epi f := Descent.Construction.quotient_epi i f hkernel h_FiniteDescent
  let σ : EndomorphismAction (A := B) R := {
    map := d
    preservesGroup := fun r => Picard.PoincareBundle.Epi.Construction.isMonHom_of_comp f (ρ.map r ≫ f) (d r) (hd r)
    map_zero := by
      apply (cancel_epi f).mp
      rw [hd, ρ.map_zero, MonObj.one_comp, MonObj.comp_one]
    map_one := Descent.Construction.descended_identity f (d 1) (by rw [hd, ρ.map_one])
    map_add := fun r t => Descent.Construction.descended_addition f (ρ.map r) (ρ.map t)
      (d r) (d t) (d (r + t)) (hd r) (hd t) (by rw [hd, ρ.map_add])
    map_mul := fun r t => Descent.Construction.descended_composition f (ρ.map t) (ρ.map r)
      (d t) (d r) (d (r * t)) (hd t) (hd r) (by rw [hd, ρ.map_mul]) }
  refine ⟨σ, hd, ?_⟩
  intro τ hτ
  have hmaps : τ.map = σ.map := by
    funext r
    exact (cancel_epi f).mp ((hτ r).trans (hd r).symm)
  exact EndomorphismAction.ext hmaps

end Action

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]
variable {P : Over S} (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)

/-- Stability is imposed and checked on all test schemes. -/
def RelativeSubgroupStable (a : A ⟶ A) : Prop :=
  ∀ (X : Over S) (t : X ⟶ P) (x : X ⟶ A),
    x ∈ F.points X t → x ≫ a ∈ F.points X t

/-- The split integral action is scalar on a block of n-torsion, and
every subgroup of that block is stable under these integer scalars. -/
theorem relative_subgroup_stable_of_scalar
    (a : A ⟶ A) (k : ℤ)
    (hscalar : ∀ (X : Over S) (t : X ⟶ P) (x : X ⟶ A),
      x ∈ F.points X t → x ≫ a = x ^ k) :
    RelativeSubgroupStable F a := by
  intro X t x hx
  rw [hscalar X t x hx]
  exact (F.points X t).zpow_mem hx k

variable [IsCommMonObj A]

/-- Stability of both factors implies stability of their actual product
subgroup; this also permits iteration over all chosen/opposite blocks. -/
theorem relative_kernel_product_stable
    (G : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (a : A ⟶ A) [IsMonHom a]
    (hF : RelativeSubgroupStable F a) (hG : RelativeSubgroupStable G a) :
    RelativeSubgroupStable (Kernel.Product.Construction.relativeKernelProduct F G) a := by
  intro X t x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  exact ⟨y ≫ a, hF X t y hy, z ≫ a, hG X t z hz, MonObj.mul_comp y z a⟩

omit [IsCommMonObj A] in
/-- Translate stability of the functor of points to the scheme kernel
criterion required by quotient descent. -/
theorem stable_model_kernel
    (R : F.Model) (a : A ⟶ A)
    (hstable : RelativeSubgroupStable F a)
    {B : Over S} [GrpObj B] (f : A ⟶ B)
    (hkernel : ∀ (X : Over S) (t : X ⟶ P) (x : X ⟶ A),
      x ∈ F.points X t → x ≫ f = 1) :
    R.toGroup ≫ a ≫ f = 1 := by
  have hi : R.toGroup ∈ F.points R.carrier R.toBase :=
    (R.points_iff R.carrier R.toBase R.toGroup).mpr
      ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩
  exact (Category.assoc _ _ _).symm.trans
    (hkernel R.carrier R.toBase (R.toGroup ≫ a)
      (hstable R.carrier R.toBase R.toGroup hi))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Action.Construction
