import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearProducts

/-! # Quadrilinear Local Hom -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearLocalHom.Construction

noncomputable section

/-! The last input of a four-linear sheaf map gives an actual
section of the internal Hom sheaf on each open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} {M N P Q R : X.Modules}

def quadrilinearOfTrilinearHom (b : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P (Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom Q R)) :
    QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R where
  app U := (b.app U).compr₂
    (LinearMap.llcomp Γ(X, U) Γ(P, U) Γ(Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom Q R, U)
      (Γ(Q, U) →ₗ[Γ(X, U)] Γ(R, U)) (Picard.Homomorphisms.TensorHom.Construction.internalHomEval Q R U))
  naturality {U V} h m n p q := by
    change R.presheaf.map h.op (Picard.Homomorphisms.TensorHom.Construction.internalHomEval Q R U (b.app U m n p) q) =
      Picard.Homomorphisms.TensorHom.Construction.internalHomEval Q R V (b.app V (M.presheaf.map h.op m) (N.presheaf.map h.op n) (P.presheaf.map h.op p))
        (Q.presheaf.map h.op q)
    rw [← Picard.Homomorphisms.TensorHom.Construction.internalHomEval_naturality, b.naturality]

def quadrilinearLocalHom (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) : Γ(Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom Q R, U) :=
  ⟨{ app V := AddCommGrpCat.ofHom
        (b.app V.unop.left (M.presheaf.map V.unop.hom.op m)
          (N.presheaf.map V.unop.hom.op n) (P.presheaf.map V.unop.hom.op p)).toAddMonoidHom
     naturality {V W} f := by
       ext q
       have he := b.naturality f.unop.left
         (M.presheaf.map V.unop.hom.op m) (N.presheaf.map V.unop.hom.op n)
         (P.presheaf.map V.unop.hom.op p) q
       have hm : M.presheaf.map f.unop.left.op (M.presheaf.map V.unop.hom.op m) =
           M.presheaf.map W.unop.hom.op m := by
         rw [← Functor.map_comp_apply, ← op_comp, Over.w f.unop]
       have hn : N.presheaf.map f.unop.left.op (N.presheaf.map V.unop.hom.op n) =
           N.presheaf.map W.unop.hom.op n := by
         rw [← Functor.map_comp_apply, ← op_comp, Over.w f.unop]
       have hp : P.presheaf.map f.unop.left.op (P.presheaf.map V.unop.hom.op p) =
           P.presheaf.map W.unop.hom.op p := by
         rw [← Functor.map_comp_apply, ← op_comp, Over.w f.unop]
       rw [hm, hn, hp] at he
       exact he.symm },
    fun V r q => (b.app V.left (M.presheaf.map V.hom.op m)
      (N.presheaf.map V.hom.op n) (P.presheaf.map V.hom.op p)).map_smul r q⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearLocalHom.Construction
