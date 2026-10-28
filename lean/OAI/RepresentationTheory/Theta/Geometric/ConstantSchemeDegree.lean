import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Constant Scheme Degree -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConstantSchemeDegree

noncomputable section

/-! The finite-flat degree of a constant finite scheme is its number of labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

variable (F : Type) [Field F] (I : Type) [Finite I]

def constantAffineLabelsIso : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of F)) I ≅
    OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver F (I → F) := by
  let := Fintype.ofFinite I
  let e : (∐ fun _ : I => Spec (.of F)) ≅ Spec (.of (I → F)) :=
    asIso (sigmaSpec (fun _ : I => CommRingCat.of F))
  refine Over.isoMk e ?_
  apply Sigma.hom_ext
  intro i
  change Sigma.ι _ i ≫ sigmaSpec (fun _ : I => CommRingCat.of F) ≫
    Spec.map (CommRingCat.ofHom (algebraMap F (I → F))) =
      Sigma.ι _ i ≫ Sigma.desc (fun _ : I => 𝟙 (Spec (.of F)))
  rw [ι_sigmaSpec_assoc, Sigma.ι_comp_desc, ← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap F (I → F)) ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun _ : I => F) i) = 𝟙 _ := by
    ext r
    rfl
  rw [h, Spec.map_id]

theorem constantScheme_finrank (z : Spec (.of F)) :
    (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of F)) I).hom.finrank z = Nat.card I := by
  let := Fintype.ofFinite I
  let e := constantAffineLabelsIso F I
  let : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget (Spec (.of F))).mapIso e).inv))
  let : Flat (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of F)) I).hom :=
    (Etale.iff_flat_and_formallyUnramified.mp inferInstance).1
  calc
    _ = (e.inv.left ≫ (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of F)) I).hom).finrank z := by
      rw [Scheme.Hom.finrank_comp_left_of_isIso]
    _ = (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver F (I → F)).hom.finrank z :=
      congrArg (fun f => Scheme.Hom.finrank f z) e.inv.w
    _ = Nat.card I := by
      change (Spec.map (CommRingCat.ofHom (algebraMap F (I → F)))).finrank z = _
      refine (Scheme.Hom.finrank_SpecMap_algebraMap F (I → F) z).trans ?_
      rw [Module.rankAtStalk_eq_finrank_of_free]
      change Module.finrank F (I → F) = Nat.card I
      simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, mul_one, Nat.card_eq_fintype_card]

end

end OAI.RepresentationTheory.Theta.Geometric.ConstantSchemeDegree
