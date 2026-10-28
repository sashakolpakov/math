import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PairedKernels
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation

/-! # Intrinsic Annihilator Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicAnnihilatorPoints.Construction

noncomputable section

/-! All-test factorization through the native opposite kernel is exactly
vanishing of its character evaluations on the chosen subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {G H B : Grp (Over (Spec (.of k)))}
variable (P : CartierModel.Construction.CartierCoordinates (.of k) G) (Q : CartierModel.Construction.CartierCoordinates (.of k) H) (i : H ⟶ G)

theorem cartierRestriction_trivial_iff (T : Over (Spec (.of k))) (d : T ⟶ P.dualGroup.X) :
    Functor.whiskerLeft (Over.forget T).op (yonedaGrp.map i) ≫ P.pointsEquiv T d = 1 ↔
      ∀ (U : Over T) (h : U.left ⟶ H.X), ((P.pointsEquiv T d).app (.op U)) (h ≫ i.hom.hom) = 1 := by
  constructor
  · intro he U h
    exact congrArg (fun f => (f.app (.op U)) h) he
  · intro he
    apply NatTrans.ext
    funext U
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro h
    exact he U.unop h

omit Q i in
theorem cartierCharacter_sliceValue (T : Over (Spec (.of k))) (d : T ⟶ P.dualGroup.X)
    (U : Over T) (x : U.left ⟶ G.X) :
    ((P.pointsEquiv T d).app (.op U)) x =
      ((P.pointsEquiv U.left (U.hom ≫ d)).app (.op (Over.mk (𝟙 U.left)))) x := by
  obtain ⟨V, f, rfl⟩ := U.mk_surjective
  have hn := P.characterRepresentation.homEquiv_comp f d
  have h := congrArg (fun c => CartierDuality.Evaluation.Construction.CharacterEvaluation.value c x) hn
  exact (h.trans (CartierDuality.Evaluation.Construction.CharacterEvaluation.value_restrict f (P.pointsEquiv T d) x)).symm

variable (e : B ≅ P.dualGroup)

theorem oppositeInclusion_factor_iff (T : Over (Spec (.of k))) (y : T ⟶ B.X) :
    (∃ z : T ⟶ (P.annihilatorGroup Q i).X, z ≫ (P.oppositeInclusion Q i e).hom.hom = y) ↔
      ∀ (U : Over T) (h : U.left ⟶ H.X),
        ((P.pointsEquiv U.left ((U.hom ≫ y) ≫ e.hom.hom.hom)).app
          (.op (Over.mk (𝟙 U.left)))) (h ≫ i.hom.hom) = 1 := by
  let d := y ≫ e.hom.hom.hom
  have hi (z : T ⟶ (P.annihilatorGroup Q i).X) :
      z ≫ (P.oppositeInclusion Q i e).hom.hom = y ↔
        z ≫ (P.annihilatorInclusion Q i).hom.hom = d := by
    change z ≫ ((P.annihilatorInclusion Q i).hom.hom ≫ e.inv.hom.hom) = y ↔ _
    rw [← Category.assoc]
    exact ((Grp.forget (Over (Spec (.of k)))).mapIso e).comp_inv_eq
  have hf : (∃ z : T ⟶ (P.annihilatorGroup Q i).X,
      z ≫ (P.annihilatorInclusion Q i).hom.hom = d) ↔
      Functor.whiskerLeft (Over.forget T).op (yonedaGrp.map i) ≫ P.pointsEquiv T d = 1 := by
    constructor
    · rintro ⟨z, hz⟩
      apply (P.annihilator_universal Q i T d).mpr
      refine ⟨z, hz, ?_⟩
      intro w hw
      exact (cancel_mono (P.annihilatorInclusion Q i).hom.hom).mp (hw.trans hz.symm)
    · intro h
      obtain ⟨z, hz, _⟩ := (P.annihilator_universal Q i T d).mp h
      exact ⟨z, hz⟩
  rw [show (∃ z, z ≫ (P.oppositeInclusion Q i e).hom.hom = y) ↔
    (∃ z, z ≫ (P.annihilatorInclusion Q i).hom.hom = d) from exists_congr hi, hf,
    cartierRestriction_trivial_iff P i T d]
  apply forall_congr'
  intro U
  apply forall_congr'
  intro h
  have hv := cartierCharacter_sliceValue P T d U (h ≫ i.hom.hom)
  have ha := congrArg (fun z => ((P.pointsEquiv U.left z).app (.op (Over.mk (𝟙 U.left))))
    (h ≫ i.hom.hom)) (Category.assoc U.hom y e.hom.hom.hom).symm
  exact iff_of_eq (congrArg (fun z => z = 1) (hv.trans ha))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicAnnihilatorPoints.Construction
