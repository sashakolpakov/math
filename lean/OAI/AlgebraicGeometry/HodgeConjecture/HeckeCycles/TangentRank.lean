import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableTangentEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockTangentCoordinates

/-! # Tangent Rank -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TangentRank.CM

noncomputable section

/-! Tangent rank uses the original scheme maps and dual-number scalar
operations. Standard multiplicative factors have their expected rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k]

def Points (G : Grp (Over (Spec (.of k)))) :=
  {p : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ G.X // AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ p = 1}

def HasRank (G : Grp (Over (Spec (.of k)))) (d : ℕ) : Prop :=
  ∃ e : (Fin d → k) ≃ Points G,
    (∀ x y, (e (x + y)).val = (e x).val * (e y).val) ∧
    (∀ (a : k) x, (e (a • x)).val = AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k a ≫ (e x).val)

def pointsEquiv {G H : Grp (Over (Spec (.of k)))} (e : G ≅ H) : Points G ≃ Points H where
  toFun p := ⟨p.val ≫ e.hom.hom.hom, by
    rw [← Category.assoc, p.property, MonObj.one_comp]⟩
  invFun p := ⟨p.val ≫ e.inv.hom.hom, by
    rw [← Category.assoc, p.property, MonObj.one_comp]⟩
  left_inv p := by
    apply Subtype.ext
    change (p.val ≫ ((Grp.forget _).mapIso e).hom) ≫ ((Grp.forget _).mapIso e).inv = p.val
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => p.val ≫ z) ((Grp.forget _).mapIso e).hom_inv_id).trans
        (Category.comp_id _))
  right_inv p := by
    apply Subtype.ext
    change (p.val ≫ ((Grp.forget _).mapIso e).inv) ≫ ((Grp.forget _).mapIso e).hom = p.val
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => p.val ≫ z) ((Grp.forget _).mapIso e).inv_hom_id).trans
        (Category.comp_id _))

theorem rank_transport {G H : Grp (Over (Spec (.of k)))} (e : G ≅ H) {d : ℕ}
    (h : HasRank G d) : HasRank H d := by
  obtain ⟨c, ha, hs⟩ := h
  refine ⟨c.trans (pointsEquiv e), ?_, ?_⟩
  · intro x y
    change (c (x + y)).val ≫ e.hom.hom.hom = _
    rw [ha, MonObj.mul_comp]
    rfl
  · intro a x
    change (c (a • x)).val ≫ e.hom.hom.hom = _
    rw [hs, Category.assoc]
    rfl

theorem rank_unique {G : Grp (Over (Spec (.of k)))} {d r : ℕ}
    (hd : HasRank G d) (hr : HasRank G r) : d = r := by
  obtain ⟨e, ea, es⟩ := hd
  obtain ⟨f, fa, fs⟩ := hr
  let u : (Fin d → k) ≃ₗ[k] (Fin r → k) := {
    toEquiv := e.trans f.symm
    map_add' := fun x y => by
      apply f.injective
      apply Subtype.ext
      change (f (f.symm (e (x + y)))).val = (f (f.symm (e x) + f.symm (e y))).val
      rw [f.apply_symm_apply, ea, fa, f.apply_symm_apply, f.apply_symm_apply]
    map_smul' := fun a x => by
      apply f.injective
      apply Subtype.ext
      change (f (f.symm (e (a • x)))).val = (f (a • f.symm (e x))).val
      rw [f.apply_symm_apply, es, fs, f.apply_symm_apply] }
  simpa using u.finrank_eq

theorem scalar_nat {G : Grp (Over (Spec (.of k)))} [IsCommMonObj G.X] {d : ℕ}
    (h : HasRank G d) (p : Points G) (m : ℕ) :
    AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k (m : k) ≫ p.val = p.val ^ m := by
  obtain ⟨e, ha, hs⟩ := h
  let f : (Fin d → k) →+ Additive (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ G.X) := {
    toFun x := Additive.ofMul (e x).val
    map_zero' := by
      have hz := ha 0 0
      rw [add_zero] at hz
      exact congrArg Additive.ofMul (mul_eq_left.mp hz.symm)
    map_add' x y := congrArg Additive.ofMul (ha x y) }
  obtain ⟨x, rfl⟩ := e.surjective p
  rw [← hs, Nat.cast_smul_eq_nsmul]
  exact congrArg Additive.toMul (f.map_nsmul m x)

theorem multiplicative_rank (q n d : ℕ) [Fact q.Prime] [CharP k q] :
    HasRank (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q (n + 1) d) d := by
  let e := (BlockTangentCoordinates.CM.characterEquiv k q n d).symm
  let t := DiagonalizableTangentEquiv.CM.tangentEquiv
    (k := k) (M := AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q (n + 1) d)
  refine ⟨e.toEquiv.trans t, ?_, ?_⟩
  · intro x y
    change RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point (e (x + y)) = _
    rw [map_add, RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point_add]
    rfl
  · intro a x
    change RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point (e (a • x)) = _
    rw [map_smul, ← RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point_scalar]
    rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TangentRank.CM
