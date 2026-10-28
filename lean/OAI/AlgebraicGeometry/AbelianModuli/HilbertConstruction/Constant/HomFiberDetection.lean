import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.FamilyMapRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Hom Fiber Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! One field-valued fiber detects zero homomorphisms between constant abelian families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem Abelian.Schemes.AbelianScheme.hom_killed_by_baseChange {S U : Scheme.{u}} {g h : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S) (s : U ⟶ S)
    (f : A.scheme ⟶ B.scheme) (hf : (Over.pullback s).map f = 1) :
    Limits.pullback.fst A.scheme.hom s ≫ f.left =
      Limits.pullback.snd A.scheme.hom s ≫ s ≫ η[B.scheme].left := by
  let T := (A.pullback s).scheme
  let E := B.baseChangePointsMulEquiv s T
  have he : A.baseChangePointsMulEquiv s T (𝟙 T) ≫ f = 1 := by
    calc
      A.baseChangePointsMulEquiv s T (𝟙 T) ≫ f =
          E (𝟙 T ≫ (Over.pullback s).map f) := (Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map f s T (𝟙 T)).symm
      _ = E 1 := congrArg E ((congrArg (fun q => 𝟙 T ≫ q) hf).trans (MonObj.comp_one (𝟙 T)))
      _ = 1 := map_one E
  have hh := congrArg Over.Hom.left he
  change (𝟙 (Limits.pullback A.scheme.hom s) ≫ Limits.pullback.fst A.scheme.hom s) ≫ f.left =
    (Limits.pullback.snd A.scheme.hom s ≫ s) ≫ η[B.scheme].left at hh
  exact (congrArg (fun q => q ≫ f.left) (Category.id_comp _)).symm.trans
    (hh.trans (Category.assoc _ _ _))

theorem Abelian.Schemes.AbelianScheme.pullback_hom_eq_one_of_field_fiber
    {K F : Type u} [Field K] [Field F] {g h : ℕ} {T : Scheme.{u}}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))
    (t : T ⟶ Spec (.of K)) [PreconnectedSpace T]
    (f : (A.pullback t).scheme ⟶ (B.pullback t).scheme) [IsMonHom f]
    (s : Spec (.of F) ⟶ T) (hf : (Over.pullback s).map f = 1) : f = 1 := by
  let a : Spec (.of F) ⟶ B.scheme.left :=
    s ≫ η[(B.pullback t).scheme].left ≫ Limits.pullback.fst B.scheme.hom t
  let v : Spec (.of F) := default
  apply A.pullback_hom_eq_one_of_constant_fiber B t f (s v) (a v)
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

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
