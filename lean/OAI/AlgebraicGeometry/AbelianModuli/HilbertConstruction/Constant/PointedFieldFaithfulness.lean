import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.PointedMapRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.HomFiberDetection

/-! # Pointed Field Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A single field-valued point detects identity-preserving morphisms between constant abelian families on connected test schemes, including nonreduced tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem Abelian.Schemes.AbelianScheme.pullback_pointedMap_eq_one_of_field_fiber
    {K F : Type u} [Field K] [Field F] {g h : ℕ} {T : Scheme.{u}}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))
    (t : T ⟶ Spec (.of K)) [PreconnectedSpace T]
    (f : (A.pullback t).scheme ⟶ (B.pullback t).scheme)
    (hpoint : η[(A.pullback t).scheme] ≫ f = η[(B.pullback t).scheme])
    (s : Spec (.of F) ⟶ T) (hf : (Over.pullback s).map f = 1) : f = 1 := by
  let a : Spec (.of F) ⟶ B.scheme.left :=
    s ≫ η[(B.pullback t).scheme].left ≫ Limits.pullback.fst B.scheme.hom t
  let v : Spec (.of F) := default
  apply A.pullback_pointedMap_eq_one_of_constant_fiber B t f hpoint (s v) (a v)
  intro z hz
  have hr : z ∈ Set.range (Limits.pullback.fst (A.pullback t).scheme.hom s) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨v, hz.symm⟩
  obtain ⟨w, rfl⟩ := hr
  have H := Abelian.Schemes.AbelianScheme.hom_killed_by_baseChange (A.pullback t) (B.pullback t) s f hf
  have he := congrArg (fun q : Limits.pullback (A.pullback t).scheme.hom s ⟶
      (B.pullback t).scheme.left => q w) H
  exact (congrArg (fun b => Limits.pullback.fst B.scheme.hom t b) he).trans
    (congrArg a (Subsingleton.elim (Limits.pullback.snd (A.pullback t).scheme.hom s w) v))

theorem Abelian.Schemes.AbelianScheme.pullback_pointedMaps_eq_of_field_fiber
    {K F : Type u} [Field K] [Field F] {g h : ℕ} {T : Scheme.{u}}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))
    (t : T ⟶ Spec (.of K)) [PreconnectedSpace T] (s : Spec (.of F) ⟶ T)
    (f q : (A.pullback t).scheme ⟶ (B.pullback t).scheme)
    (hpoint : η[(A.pullback t).scheme] ≫ f = η[(A.pullback t).scheme] ≫ q)
    (hfq : (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  apply div_eq_one.mp
  refine A.pullback_pointedMap_eq_one_of_field_fiber B t (f / q) ?_ s ?_
  · rw [GrpObj.comp_div, hpoint]
    exact (div_self' (η[(A.pullback t).scheme] ≫ q)).trans (MonObj.one_eq_one _).symm
  · rw [div_eq_mul_inv, Functor.map_mul, Functor.map_inv', hfq, mul_inv_cancel]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
