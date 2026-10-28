import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.FamilyMapRigidity

/-! # Pointed Map Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A map between constant abelian families that preserves the identity and is constant on one fiber is the zero map; no homomorphism hypothesis is required. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g h : ℕ} {T : Scheme.{u}}

theorem Abelian.Schemes.AbelianScheme.pullback_pointedMap_eq_one_of_constant_fiber
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))
    (t : T ⟶ Spec (.of K)) [PreconnectedSpace T]
    (f : (A.pullback t).scheme ⟶ (B.pullback t).scheme)
    (hpoint : η[(A.pullback t).scheme] ≫ f = η[(B.pullback t).scheme])
    (s : T) (y : B.scheme.left)
    (hy : ∀ z : (A.pullback t).scheme.left, (A.pullback t).scheme.hom z = s →
      Limits.pullback.fst B.scheme.hom t (f.left z) = y) : f = 1 := by
  have : B.scheme.left.IsSeparated := by
    have : IsSeparated (B.scheme.hom ≫ Limits.terminal.from (Spec (.of K))) := inferInstance
    rw [Limits.terminal.comp_from] at this
    exact ⟨this⟩
  have H := A.pullback_map_rigidity t (f.left ≫ Limits.pullback.fst B.scheme.hom t) s y hy
  have hunit : η[(A.pullback t).scheme].left ≫ f.left = η[(B.pullback t).scheme].left :=
    congrArg Over.Hom.left hpoint
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · calc
      f.left ≫ Limits.pullback.fst B.scheme.hom t =
          (A.pullback t).scheme.hom ≫ η[(A.pullback t).scheme].left ≫
            f.left ≫ Limits.pullback.fst B.scheme.hom t := H
      _ = (A.pullback t).scheme.hom ≫ η[(B.pullback t).scheme].left ≫
          Limits.pullback.fst B.scheme.hom t :=
        congrArg (fun q : T ⟶ B.scheme.left => (A.pullback t).scheme.hom ≫ q)
          ((Category.assoc η[(A.pullback t).scheme].left f.left
            (Limits.pullback.fst B.scheme.hom t)).symm.trans
            (congrArg (fun q : T ⟶ (B.pullback t).scheme.left =>
              q ≫ Limits.pullback.fst B.scheme.hom t) hunit))
      _ = (1 : (A.pullback t).scheme ⟶ (B.pullback t).scheme).left ≫
          Limits.pullback.fst B.scheme.hom t := (Category.assoc _ _ _).symm
  · exact f.w.trans (1 : (A.pullback t).scheme ⟶ (B.pullback t).scheme).w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
