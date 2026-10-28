import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Ordinary

/-! # Reduced Height One Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReducedHeightOneMaps.Construction

noncomputable section

/-!
A morphism from a reduced test scheme to a group with trivial relative
Frobenius is the identity-valued map. This supplies the vanishing of
cross maps from the etale part to the multiplicative q-torsion part,
needed to make the active etale subgroup independent of a splitting.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)
variable {X M : Over S} [IsReduced X.left] [GrpObj M]

/-- Reduced test schemes see only the identity in a height-one
infinitesimal group, as an equality of actual scheme morphisms. -/
theorem map_from_reduced_of_trivial_frobenius (f : X ⟶ M)
    (hM : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS M = 1) : f = 1 := by
  let hX := Picard.Homomorphisms.Frobenius.Construction.prime_eq_zero_of_map p hS X.hom
  let hY := Picard.Homomorphisms.Frobenius.Construction.prime_eq_zero_of_map p hS M.hom
  let FX := Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X.left hX
  let FM := Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp M.left hY
  have hn : FX ≫ f.left = f.left ≫ FM :=
    Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius_naturality p hp hX hY f.left
  have hz : FX ≫ (1 : X ⟶ M).left = (1 : X ⟶ M).left ≫ FM :=
    Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius_naturality p hp hX hY (1 : X ⟶ M).left
  let t : (Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS M).left ⟶ M.left :=
    CategoryTheory.Limits.pullback.fst M.hom (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)
  have ht : FM = (1 : M ⟶ Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS M).left ≫ t :=
    (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius_comp_fst p hp hS M).symm.trans
      (congrArg (fun z : M ⟶ Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS M => z.left ≫ t) hM)
  have hconst : f.left ≫ FM = (1 : X ⟶ M).left ≫ FM := by
    rw [ht, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun z : X ⟶ Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist p hp hS M => z.left ≫ t)
      ((MonObj.comp_one f).trans (MonObj.comp_one (1 : X ⟶ M)).symm)
  apply Over.OverMorphism.ext
  exact (cancel_epi FX).mp (hn.trans (hconst.trans hz.symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReducedHeightOneMaps.Construction
