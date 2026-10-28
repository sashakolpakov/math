import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearLocalHom

/-! # Quadrilinear Local Linearity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearLocalLinearity.Construction

noncomputable section

/-! The local internal-Hom section is linear in each of the three
remaining inputs. Each law is checked on actual restricted sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} {M N P Q R : X.Modules}
  (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R) (U : X.Opens)

theorem quadrilinearLocalHom_add_first (m m' : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U (m + m') n p = QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n p + QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m' n p := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro q
  change b.app V.unop.left (M.presheaf.map V.unop.hom.op (m + m')) _ _ q =
    b.app V.unop.left (M.presheaf.map V.unop.hom.op m) _ _ q +
      b.app V.unop.left (M.presheaf.map V.unop.hom.op m') _ _ q
  erw [map_add, map_add, LinearMap.add_apply]

theorem quadrilinearLocalHom_smul_first (r : Γ(X, U)) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U (r • m) n p = r • QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n p := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro q
  change b.app V.unop.left (M.presheaf.map V.unop.hom.op (r • m)) _ _ q =
    X.presheaf.map V.unop.hom.op r • b.app V.unop.left (M.presheaf.map V.unop.hom.op m) _ _ q
  erw [M.val.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rfl

theorem quadrilinearLocalHom_add_second (m : Γ(M, U)) (n n' : Γ(N, U)) (p : Γ(P, U)) :
    QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m (n + n') p = QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n p + QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n' p := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro q
  change b.app V.unop.left _ (N.presheaf.map V.unop.hom.op (n + n')) _ q =
    b.app V.unop.left _ (N.presheaf.map V.unop.hom.op n) _ q +
      b.app V.unop.left _ (N.presheaf.map V.unop.hom.op n') _ q
  erw [map_add, map_add, LinearMap.add_apply]

theorem quadrilinearLocalHom_smul_second (r : Γ(X, U)) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m (r • n) p = r • QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n p := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro q
  change b.app V.unop.left _ (N.presheaf.map V.unop.hom.op (r • n)) _ q =
    X.presheaf.map V.unop.hom.op r • b.app V.unop.left _ (N.presheaf.map V.unop.hom.op n) _ q
  erw [N.val.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rfl

theorem quadrilinearLocalHom_add_third (m : Γ(M, U)) (n : Γ(N, U)) (p p' : Γ(P, U)) :
    QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n (p + p') = QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n p + QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n p' := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro q
  change b.app V.unop.left _ _ (P.presheaf.map V.unop.hom.op (p + p')) q =
    b.app V.unop.left _ _ (P.presheaf.map V.unop.hom.op p) q +
      b.app V.unop.left _ _ (P.presheaf.map V.unop.hom.op p') q
  erw [map_add, map_add, LinearMap.add_apply]

theorem quadrilinearLocalHom_smul_third (r : Γ(X, U)) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n (r • p) = r • QuadrilinearLocalHom.Construction.quadrilinearLocalHom b U m n p := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro q
  change b.app V.unop.left _ _ (P.presheaf.map V.unop.hom.op (r • p)) q =
    X.presheaf.map V.unop.hom.op r • b.app V.unop.left _ _ (P.presheaf.map V.unop.hom.op p) q
  erw [P.val.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearLocalLinearity.Construction
