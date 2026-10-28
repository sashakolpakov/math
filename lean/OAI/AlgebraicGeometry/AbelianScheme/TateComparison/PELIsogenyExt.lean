import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualFactorization

/-! # PEL Isogeny Ext -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The abelian map determines every field of an actual PEL isogeny.
Its dual is forced by the original Poincare universal property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {R : Type u} [CommRing R] {S : Scheme.{u}} {g N n : ℕ}
  {P Q : PEL.PELFamilyData R g N S}

theorem PELIsogenies.PELIsogeny.eq_of_hom_eq (e f : PELIsogenies.PELIsogeny P Q n) (h : e.isogeny.hom = f.isogeny.hom) : e = f := by
  have hi : e.isogeny = f.isogeny := by
    have ext : ∀ (a b : P.abelian.Isogeny Q.abelian), a.hom = b.hom → a = b := by
      rintro ⟨a, _, _, _, _⟩ ⟨b, _, _, _, _⟩ hab
      cases hab
      rfl
    exact ext e.isogeny f.isogeny h
  have hd : e.dualHom = f.dualHom := by
    apply Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_injective P.dual Q.dual.abelian.scheme
    rw [CentralAction.DualFactorization.Construction.pelIsogeny_poincareClass, CentralAction.DualFactorization.Construction.pelIsogeny_poincareClass, h]
  cases e
  cases f
  cases hi
  cases hd
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
