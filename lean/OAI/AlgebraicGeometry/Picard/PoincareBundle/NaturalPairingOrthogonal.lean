import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Natural Pairing Orthogonal -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal

noncomputable section

/-!
# Orthogonality for a bilinear pairing on arbitrary scheme-valued points

Orthogonality is tested after every further change of test scheme. Thus the definition retains
the full subgroup functor, including infinitesimal test points, and is stable under base change.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H G : Over S} [GrpObj G] (i : H ⟶ G)
  (e : ∀ T : Over S, (T ⟶ G) →* (T ⟶ G) →* Γ(T.left, ⊤)ˣ)

/-- The right orthogonal subgroup is tested on all scheme points after every further base change. -/
def orthogonal (T : Over S) : Subgroup (T ⟶ G) where
  carrier := {y | ∀ (U : Over S) (a : U ⟶ T) (k : U ⟶ H), e U (k ≫ i) (a ≫ y) = 1}
  one_mem' := by intro U a k; rw [MonObj.comp_one, map_one]
  mul_mem' := by
    intro y z hy hz U a k
    rw [MonObj.comp_mul, map_mul, hy U a k, hz U a k, one_mul]
  inv_mem' := by
    intro y hy U a k
    rw [GrpObj.comp_inv, map_inv, hy U a k, inv_one]

/-- The full orthogonality condition is preserved by arbitrary morphisms of test schemes. -/
theorem orthogonal_baseChange {T U : Over S} (a : U ⟶ T) (y : T ⟶ G)
    (hy : y ∈ orthogonal i e T) : a ≫ y ∈ orthogonal i e U := by
  intro V b k
  exact (congrArg (fun z => e V (k ≫ i) z) (Category.assoc b a y).symm).trans (hy V (b ≫ a) k)

/-- Self-annihilation identifies the full orthogonal subfunctor with the represented subgroup. -/
def SelfAnnihilating : Prop := ∀ (T : Over S) (y : T ⟶ G),
  y ∈ orthogonal i e T ↔ ∃ k : T ⟶ H, k ≫ i = y

/-- A self-annihilating represented subgroup is isotropic on every scheme-valued pair. -/
theorem isotropic_of_selfAnnihilating (h : SelfAnnihilating i e)
    {T : Over S} (k l : T ⟶ H) : e T (k ≫ i) (l ≫ i) = 1 := by
  have hl := (h T (l ≫ i)).mpr ⟨l, rfl⟩
  simpa only [Category.id_comp] using hl T (𝟙 T) k

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal
