import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RankAnnihilation
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation

/-! # Group Annihilator -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupAnnihilator

noncomputable section

/-! A positive integer annihilates an actual finite commutative group
scheme over a field. The Hopf algebra norm calculation retains all
infinitesimal points; reducedness is not required. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u

theorem group_power_of_iso {S : Scheme.{u}} {G H : Grp (Over S)}
    (e : G ≅ H) (n : ℕ) (hG : (𝟙 G.X) ^ n = 1) : (𝟙 H.X) ^ n = 1 := by
  let a : H.X ⟶ G.X := e.inv.hom.hom
  let b : G.X ⟶ H.X := e.hom.hom.hom
  have : IsMonHom b := inferInstanceAs (IsMonHom e.hom.hom.hom)
  have he : a ≫ b = 𝟙 H.X := congrArg (fun f : H ⟶ H => f.hom.hom) e.inv_hom_id
  have ha : a ^ n = 1 :=
    (congrArg (fun f => f ^ n) (Category.comp_id a)).symm.trans
      ((MonObj.comp_pow (𝟙 G.X) n a).symm.trans
        ((congrArg (fun f => a ≫ f) hG).trans (MonObj.comp_one a)))
  exact (congrArg (fun f => f ^ n) he).symm.trans
    ((MonObj.pow_comp a n b).symm.trans
      ((congrArg (fun f => f ≫ b) ha).trans (MonObj.one_comp b)))

theorem finiteGroup_exists_annihilator (k : Type u) [Field k]
    (G : Grp (Over (Spec (CommRingCat.of k)))) [IsCommMonObj G.X] [IsFinite G.X.hom] :
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X), x ^ n = 1 := by
  obtain ⟨R, hR, hc, ⟨e⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  have : Module.Finite k R := hR
  have : Coalgebra.IsCocomm k R := hc
  have : Nontrivial R := (Bialgebra.counitAlgHom k R).toRingHom.domain_nontrivial
  have hp : (𝟙 ((hopfSpec (CommRingCat.of k)).obj (.op R)).X) ^ Module.finrank k R = 1 := by
    have h := AbelianScheme.CartierDuality.RankAnnihilation.Construction.NormCharacters.affineGroup_power_card k R (Module.finBasis k R)
    simp only [Fintype.card_fin] at h
    change (𝟙 ((hopfSpec (CommRingCat.of k)).obj (.op R)).X) ^ Module.finrank k R = 1 at h
    exact h
  have hG := group_power_of_iso e (Module.finrank k R) hp
  refine ⟨Module.finrank k R, Module.finrank_pos, fun T x => ?_⟩
  have h := congrArg (fun a : G.X ⟶ G.X => x ≫ a) hG
  simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using h

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupAnnihilator
