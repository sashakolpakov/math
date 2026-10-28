import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearLocalLinearity

/-! # Quadrilinear Curry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearCurry.Construction

noncomputable section

/-! Currying the fourth input is an actual equivalence between
four-linear maps and trilinear maps into the internal Hom sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} {M N P Q R : X.Modules}

def quadrilinearLocalHomMap (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(P, U) →ₗ[Γ(X, U)] Γ(Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom Q R, U) where
  toFun m :=
    { toFun n :=
        { toFun := QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n
          map_add' := QuadrilinearLocalLinearity.Construction.quadrilinearLocalHom_add_third b U m n
          map_smul' r p := QuadrilinearLocalLinearity.Construction.quadrilinearLocalHom_smul_third b U r m n p }
      map_add' n n' := by
        ext p
        exact QuadrilinearLocalLinearity.Construction.quadrilinearLocalHom_add_second b U m n n' p
      map_smul' r n := by
        ext p
        exact QuadrilinearLocalLinearity.Construction.quadrilinearLocalHom_smul_second b U r m n p }
  map_add' m m' := by
    ext n p
    exact QuadrilinearLocalLinearity.Construction.quadrilinearLocalHom_add_first b U m m' n p
  map_smul' r m := by
    ext n p
    exact QuadrilinearLocalLinearity.Construction.quadrilinearLocalHom_smul_first b U r m n p

theorem quadrilinearLocalHom_natural (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R)
    {U V : X.Opens} (h : V ⟶ U) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    (Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom Q R).presheaf.map h.op (QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n p) =
      QuadrilinearLocalHom.Construction.quadrilinearLocalHom b V (M.presheaf.map h.op m) (N.presheaf.map h.op n) (P.presheaf.map h.op p) := by
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.ext
  intro q
  change b.app W.unop.left (M.presheaf.map (W.unop.hom ≫ h).op m)
      (N.presheaf.map (W.unop.hom ≫ h).op n) (P.presheaf.map (W.unop.hom ≫ h).op p) q =
    b.app W.unop.left (M.presheaf.map W.unop.hom.op (M.presheaf.map h.op m))
      (N.presheaf.map W.unop.hom.op (N.presheaf.map h.op n))
      (P.presheaf.map W.unop.hom.op (P.presheaf.map h.op p)) q
  simp only [op_comp, Functor.map_comp_apply]

def trilinearHomOfQuadrilinear (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R) :
    Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P (Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom Q R) where
  app U := quadrilinearLocalHomMap b U
  naturality h m n p := quadrilinearLocalHom_natural b h m n p

theorem quadrilinear_trilinear_roundtrip (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R) :
    QuadrilinearLocalHom.Construction.quadrilinearOfTrilinearHom (trilinearHomOfQuadrilinear b) = b := by
  ext U m n p q
  change b.app U (M.presheaf.map (𝟙 U).op m) (N.presheaf.map (𝟙 U).op n)
      (P.presheaf.map (𝟙 U).op p) q = b.app U m n p q
  rw [op_id, M.presheaf.map_id, N.presheaf.map_id, P.presheaf.map_id,
    AddCommGrpCat.id_apply, AddCommGrpCat.id_apply, AddCommGrpCat.id_apply]

theorem trilinear_quadrilinear_roundtrip (b : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P (Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom Q R)) :
    trilinearHomOfQuadrilinear (QuadrilinearLocalHom.Construction.quadrilinearOfTrilinearHom b) = b := by
  ext U m n p
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro q
  change Picard.Homomorphisms.TensorHom.Construction.internalHomEval Q R V.unop.left
      (b.app V.unop.left (M.presheaf.map V.unop.hom.op m)
        (N.presheaf.map V.unop.hom.op n) (P.presheaf.map V.unop.hom.op p)) q =
    (b.app U m n p).val.app V q
  exact congrArg (fun a => Picard.Homomorphisms.TensorHom.Construction.internalHomEval Q R V.unop.left a q) (b.naturality V.unop.hom m n p).symm

def trilinearHomQuadrilinearEquiv :
    Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P (Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom Q R) ≃ QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R where
  toFun := QuadrilinearLocalHom.Construction.quadrilinearOfTrilinearHom
  invFun := trilinearHomOfQuadrilinear
  left_inv := trilinear_quadrilinear_roundtrip
  right_inv := quadrilinear_trilinear_roundtrip

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearCurry.Construction
