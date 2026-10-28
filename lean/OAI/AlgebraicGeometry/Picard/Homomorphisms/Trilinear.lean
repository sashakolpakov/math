import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorHom

/-! # Trilinear -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Trilinear

noncomputable section

/-! Trilinear sheaf maps and currying the last argument. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}}

structure SheafTrilinearMap (L M N P : X.Modules) where
  app (U : X.Opens) : Γ(L, U) →ₗ[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(P, U)
  naturality {U V : X.Opens} (f : V ⟶ U) (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    P.presheaf.map f.op (app U l m n) =
      app V (L.presheaf.map f.op l) (M.presheaf.map f.op m) (N.presheaf.map f.op n)

variable {L M N P : X.Modules}

@[ext]
theorem SheafTrilinearMap.ext {b c : SheafTrilinearMap L M N P}
    (h : ∀ U, b.app U = c.app U) : b = c := by
  cases b
  cases c
  congr
  exact funext h

def trilinearOfBilinearHom (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L M (InternalHom.Construction.moduleInternalHom N P)) :
    SheafTrilinearMap L M N P where
  app U := (b.app U).compr₂ (TensorHom.Construction.internalHomEval N P U)
  naturality {U V} f l m n := by
    change P.presheaf.map f.op (TensorHom.Construction.internalHomEval N P U (b.app U l m) n) =
      TensorHom.Construction.internalHomEval N P V
        (b.app V (L.presheaf.map f.op l) (M.presheaf.map f.op m)) (N.presheaf.map f.op n)
    rw [← TensorHom.Construction.internalHomEval_naturality, b.naturality]

def trilinearLocalHom (b : SheafTrilinearMap L M N P) (U : X.Opens)
    (l : Γ(L, U)) (m : Γ(M, U)) : Γ(InternalHom.Construction.moduleInternalHom N P, U) :=
  ⟨{ app V := AddCommGrpCat.ofHom
        (b.app V.unop.left (L.presheaf.map V.unop.hom.op l)
          (M.presheaf.map V.unop.hom.op m)).toAddMonoidHom
     naturality {V W} f := by
       ext n
       have he := b.naturality f.unop.left
         (L.presheaf.map V.unop.hom.op l) (M.presheaf.map V.unop.hom.op m) n
       have hl : L.presheaf.map f.unop.left.op (L.presheaf.map V.unop.hom.op l) =
           L.presheaf.map W.unop.hom.op l := by
         rw [← Functor.map_comp_apply, ← op_comp, Over.w f.unop]
       have hm : M.presheaf.map f.unop.left.op (M.presheaf.map V.unop.hom.op m) =
           M.presheaf.map W.unop.hom.op m := by
         rw [← Functor.map_comp_apply, ← op_comp, Over.w f.unop]
       rw [hl, hm] at he
       exact he.symm },
    fun V r n => (b.app V.left (L.presheaf.map V.hom.op l)
      (M.presheaf.map V.hom.op m)).map_smul r n⟩

def bilinearHomOfTrilinear (b : SheafTrilinearMap L M N P) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L M (InternalHom.Construction.moduleInternalHom N P) where
  app U :=
    { toFun l :=
        { toFun := trilinearLocalHom b U l
          map_add' m m' := by
            apply Subtype.ext
            apply NatTrans.ext
            funext V
            apply AddCommGrpCat.ext
            intro n
            change b.app V.unop.left _ (M.presheaf.map V.unop.hom.op (m + m')) n =
              b.app V.unop.left _ (M.presheaf.map V.unop.hom.op m) n +
                b.app V.unop.left _ (M.presheaf.map V.unop.hom.op m') n
            erw [map_add, map_add, LinearMap.add_apply]
          map_smul' r m := by
            apply Subtype.ext
            apply NatTrans.ext
            funext V
            apply AddCommGrpCat.ext
            intro n
            change b.app V.unop.left _ (M.presheaf.map V.unop.hom.op (r • m)) n =
              X.presheaf.map V.unop.hom.op r • b.app V.unop.left _ (M.presheaf.map V.unop.hom.op m) n
            erw [M.val.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
            rfl }
      map_add' l l' := by
        ext m
        apply Subtype.ext
        apply NatTrans.ext
        funext V
        apply AddCommGrpCat.ext
        intro n
        change b.app V.unop.left (L.presheaf.map V.unop.hom.op (l + l')) _ n =
          b.app V.unop.left (L.presheaf.map V.unop.hom.op l) _ n +
            b.app V.unop.left (L.presheaf.map V.unop.hom.op l') _ n
        erw [map_add, map_add, LinearMap.add_apply]
      map_smul' r l := by
        ext m
        apply Subtype.ext
        apply NatTrans.ext
        funext V
        apply AddCommGrpCat.ext
        intro n
        change b.app V.unop.left (L.presheaf.map V.unop.hom.op (r • l)) _ n =
          X.presheaf.map V.unop.hom.op r • b.app V.unop.left (L.presheaf.map V.unop.hom.op l) _ n
        erw [L.val.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
        rfl }
  naturality {U V} f l m := by
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    apply AddCommGrpCat.ext
    intro n
    change b.app W.unop.left (L.presheaf.map (W.unop.hom ≫ f).op l)
        (M.presheaf.map (W.unop.hom ≫ f).op m) n =
      b.app W.unop.left (L.presheaf.map W.unop.hom.op (L.presheaf.map f.op l))
        (M.presheaf.map W.unop.hom.op (M.presheaf.map f.op m)) n
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]

theorem trilinear_bilinear_roundtrip (b : SheafTrilinearMap L M N P) :
    trilinearOfBilinearHom (bilinearHomOfTrilinear b) = b := by
  ext U l m n
  change b.app U (L.presheaf.map (𝟙 U).op l) (M.presheaf.map (𝟙 U).op m) n = b.app U l m n
  rw [op_id, L.presheaf.map_id, M.presheaf.map_id, AddCommGrpCat.id_apply, AddCommGrpCat.id_apply]

theorem bilinear_trilinear_roundtrip (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L M (InternalHom.Construction.moduleInternalHom N P)) :
    bilinearHomOfTrilinear (trilinearOfBilinearHom b) = b := by
  ext U l m
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro n
  change TensorHom.Construction.internalHomEval N P V.unop.left
      (b.app V.unop.left (L.presheaf.map V.unop.hom.op l) (M.presheaf.map V.unop.hom.op m)) n =
    (b.app U l m).val.app V n
  exact congrArg (fun a => TensorHom.Construction.internalHomEval N P V.unop.left a n) (b.naturality V.unop.hom l m).symm

def bilinearHomTrilinearEquiv :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L M (InternalHom.Construction.moduleInternalHom N P) ≃ SheafTrilinearMap L M N P where
  toFun := trilinearOfBilinearHom
  invFun := bilinearHomOfTrilinear
  left_inv := bilinear_trilinear_roundtrip
  right_inv := trilinear_bilinear_roundtrip

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Trilinear
