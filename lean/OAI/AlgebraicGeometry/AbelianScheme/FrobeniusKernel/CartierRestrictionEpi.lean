import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Cartier Restriction Epi -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierRestrictionEpi.Construction

noncomputable section

/-! Cartier characters on finite locally free subgroups extend fppf locally.
The proof uses the quotient-dual comparison and double annihilation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion.Construction

theorem cartierRestrictionToAnnihilator_epi {S : Scheme.{u}} {G K : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G K) (H : Subobject G) (he : e.IsPerfect)
    [IsIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H))] :
    Epi ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e H).arrow.op) := by
  let t := CartierDuality.SheafQuotients.Construction.Schemes.annihilatorToQuotientDual e H
  let : IsIso t := CartierDuality.SheafQuotients.Construction.Schemes.annihilatorToQuotientDual_isIso e H he
  let d : CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H)) ⟶
      CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) :=
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map t.op
  let : IsIso d := (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map_isIso t.op
  let q : G ⟶ CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H := cokernel.π H.arrow
  let p : CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H ⟶ CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) :=
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H) ≫ d
  have hq : Epi q := inferInstanceAs (Epi (cokernel.π H.arrow))
  have hp : IsIso p := (asIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H)) ≪≫ asIso d).isIso_hom
  have hqp : Epi (q ≫ p) := epi_comp' hq inferInstance
  have hf : e.flip.rightAdjoint ≫
      (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e H).arrow.op =
      q ≫ p :=
    CartierDuality.DoubleAnnihilator.Construction.SelfDuality.transpose_quotient_factor (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation
      (fun a => CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation_natural a) e.rightAdjoint (CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e H).arrow
      (cokernel.π H.arrow) t (CartierDuality.SheafQuotients.Construction.Schemes.annihilatorToQuotientDual_fac e H).symm
  exact @epi_of_epi_fac (CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) inferInstance _ _ _ _ _ (q ≫ p) hqp hf

theorem cartierRestriction_epi {S : Scheme.{u}} {G : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S} (H : Subobject G)
    (hG : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S G)
    (hH : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S)) :
    Epi ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map H.arrow.op) := by
  let e := CartierDuality.SheafEvaluation.Construction.Schemes.cartierEvaluationPairing G
  have he : e.IsPerfect := (CartierDuality.PolarizedTorsion.Construction.cartier_duality G hG).2.1
  let K := CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e H
  have hK : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (K : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) :=
    CartierDuality.PolarizedTorsion.Construction.annihilator_finiteLocallyFree e H he hG hH
  have hDG := (CartierDuality.PolarizedTorsion.Construction.cartier_duality G hG).1
  let : IsIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient K)) :=
    (CartierDuality.PolarizedTorsion.Construction.cartier_duality (CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient K) (CartierDuality.QuotientRepresentability.Construction.Schemes.sheafQuotient_finiteLocallyFree K hDG hK)).2.2.1
  have hef : e.flip.IsPerfect := by
    refine ⟨he.2, ?_⟩
    have hh : e.flip.rightAdjoint = e.leftAdjoint :=
      congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint e.flip_flip
    exact hh.symm ▸ he.1
  have h := cartierRestrictionToAnnihilator_epi e.flip K hef
  have hd : CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e.flip K = H := CartierDuality.PolarizedTorsion.Construction.annihilator_double e H he hG hH
  rw [hd] at h
  exact h

theorem cartierDualMap_epi_of_finiteLocallyFree {S : Scheme.{u}} {H G : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (i : H ⟶ G) [Mono i] (hH : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S H)
    (hG : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S G) :
    Epi ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map i.op) := by
  have hK : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (Subobject.mk i : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) :=
    hH.of_iso (Subobject.underlyingIso i).symm
  have : Epi ((CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (Subobject.mk i).arrow.op) :=
    cartierRestriction_epi (Subobject.mk i) hG hK
  rw [← Subobject.underlyingIso_arrow i, op_comp, Functor.map_comp]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierRestrictionEpi.Construction
