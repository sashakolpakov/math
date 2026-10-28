import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CommutativeSheavesAb
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation

/-! # Sheaf Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes

noncomputable section

/-!
# CartierDuality: canonical evaluation for arbitrary commutative fppf sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- Evaluating an actual character of a commutative fppf sheaf. -/
def sheafCharacterValue (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (T : Over S)
    (χ : (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G).obj.obj (Opposite.op T)) :
    G.obj.obj (Opposite.op T) →* (CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb S).obj.obj (Opposite.op T) :=
  Evaluation.Construction.CharacterEvaluation.value χ

/-- Character evaluation commutes with restriction on the big site. -/
theorem sheafCharacterValue_natural (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) {T U : Over S} (f : U ⟶ T)
    (χ : (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G).obj.obj (Opposite.op T)) (x : G.obj.obj (Opposite.op T)) :
    sheafCharacterValue G U ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G).obj.map f.op χ) (G.obj.map f.op x) =
      (CommutativeSheavesAb.Construction.Schemes.multiplicativeFppfAb S).obj.map f.op (sheafCharacterValue G T χ x) :=
  Evaluation.Construction.CharacterEvaluation.value_natural f χ x

/-- Restricting a character and then evaluating recovers its component
at the corresponding object of the slice site. -/
theorem sheafCharacterValue_restrict (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (T : Over S)
    (χ : (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G).obj.obj (Opposite.op T)) (U : Over T)
    (x : G.obj.obj (Opposite.op U.left)) :
    sheafCharacterValue G U.left ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G).obj.map U.hom.op χ) x =
      χ.app (Opposite.op U) x := by
  obtain ⟨V, f, rfl⟩ := U.mk_surjective
  exact Evaluation.Construction.CharacterEvaluation.value_restrict f χ x

/-- Source restriction of characters is adjoint to the original
morphism of commutative fppf sheaves. -/
theorem cartierDualSheafMap_value {G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (a : G ⟶ H) (T : Over S)
    (χ : (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf H).obj.obj (Opposite.op T)) (x : G.obj.obj (Opposite.op T)) :
    sheafCharacterValue G T (((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map a.op).hom.app (Opposite.op T) χ) x =
      sheafCharacterValue H T χ (a.hom.app (Opposite.op T) x) := rfl

/-- Morphisms into a character sheaf agree when all their pointwise
pairing values agree, including on every further test scheme. -/
theorem sheafDualHom_ext {G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S} {a b : G ⟶ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf H}
    (h : ∀ (T : Over S) (x : G.obj.obj (Opposite.op T)) (y : H.obj.obj (Opposite.op T)),
      sheafCharacterValue H T (a.hom.app (Opposite.op T) x) y =
        sheafCharacterValue H T (b.hom.app (Opposite.op T) x) y) : a = b := by
  apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro y
  have ha := congrArg (fun χ => sheafCharacterValue H U.unop.left χ y)
    (a.hom.naturality_apply U.unop.hom.op x)
  have hb := congrArg (fun χ => sheafCharacterValue H U.unop.left χ y)
    (b.hom.naturality_apply U.unop.hom.op x)
  have har := sheafCharacterValue_restrict H T.unop (a.hom.app T x) U.unop y
  have hbr := sheafCharacterValue_restrict H T.unop (b.hom.app T x) U.unop y
  exact har.symm.trans (ha.symm.trans
    ((h U.unop.left (G.obj.map U.unop.hom.op x) y).trans (hb.trans hbr)))

/-- Evaluation at a fixed point is an actual character of the
character sheaf on every further test object. -/
def sheafEvaluationCharacter (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (T : Over S) (x : G.obj.obj (Opposite.op T)) :
    (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G)).obj.obj (Opposite.op T) where
  app U := GrpCat.ofHom
    { toFun := fun χ => sheafCharacterValue G U.unop.left χ (G.obj.map U.unop.hom.op x)
      map_one' := rfl
      map_mul' _ _ := rfl }
  naturality := by
    intro U V f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    have h := sheafCharacterValue_natural G f.unop.left χ (G.obj.map U.unop.hom.op x)
    have hw : G.obj.map V.unop.hom.op x = G.obj.map f.unop.left.op (G.obj.map U.unop.hom.op x) := by
      rw [← G.obj.map_comp_apply, ← op_comp, f.unop.w]
    exact (congrArg (sheafCharacterValue G V.unop.left
      ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G).obj.map f.unop.left.op χ)) hw).trans h

/-- The evaluation character is multiplicative in the original point. -/
theorem sheafEvaluationCharacter_mul (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (T : Over S)
    (x y : G.obj.obj (Opposite.op T)) :
    sheafEvaluationCharacter G T (x * y) = sheafEvaluationCharacter G T x *
      sheafEvaluationCharacter G T y := by
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  change sheafCharacterValue G U.unop.left χ (G.obj.map U.unop.hom.op (x * y)) =
    sheafCharacterValue G U.unop.left χ (G.obj.map U.unop.hom.op x) *
      sheafCharacterValue G U.unop.left χ (G.obj.map U.unop.hom.op y)
  exact (congrArg (sheafCharacterValue G U.unop.left χ) ((G.obj.map U.unop.hom.op).hom.map_mul x y)).trans
    ((sheafCharacterValue G U.unop.left χ).map_mul _ _)

/-- The identity point defines the trivial evaluation character. -/
theorem sheafEvaluationCharacter_one (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (T : Over S) :
    sheafEvaluationCharacter G T 1 = 1 := by
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  change sheafCharacterValue G U.unop.left χ (G.obj.map U.unop.hom.op 1) = 1
  exact (congrArg (sheafCharacterValue G U.unop.left χ) (G.obj.map U.unop.hom.op).hom.map_one).trans
    (sheafCharacterValue G U.unop.left χ).map_one

/-- The evaluation character is natural in the test scheme. -/
theorem sheafEvaluationCharacter_natural (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) {T U : Over S} (f : U ⟶ T)
    (x : G.obj.obj (Opposite.op T)) :
    sheafEvaluationCharacter G U (G.obj.map f.op x) =
      (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G)).obj.map f.op (sheafEvaluationCharacter G T x) := by
  apply NatTrans.ext
  funext V
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  change sheafCharacterValue G V.unop.left χ (G.obj.map V.unop.hom.op (G.obj.map f.op x)) =
    sheafCharacterValue G V.unop.left χ (G.obj.map (V.unop.hom ≫ f).op x)
  exact congrArg (sheafCharacterValue G V.unop.left χ) (G.obj.map_comp_apply f.op V.unop.hom.op x).symm

/-- Canonical bidual evaluation for every commutative fppf sheaf,
defined without any assertion that it is an isomorphism. -/
def sheafBidualEvaluation (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) : G ⟶ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G) :=
  ⟨{ app T := CommGrpCat.ofHom
      { toFun := sheafEvaluationCharacter G T.unop
        map_one' := sheafEvaluationCharacter_one G T.unop
        map_mul' := sheafEvaluationCharacter_mul G T.unop }
     naturality := by
       intro T U f
       apply CommGrpCat.hom_ext
       apply MonoidHom.ext
       intro x
       exact sheafEvaluationCharacter_natural G f.unop x }⟩

/-- The defining evaluation identity holds on every test object. -/
theorem sheafBidualEvaluation_value (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (T : Over S)
    (x : G.obj.obj (Opposite.op T)) (χ : (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G).obj.obj (Opposite.op T)) :
    sheafCharacterValue (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G) T ((sheafBidualEvaluation G).hom.app (Opposite.op T) x) χ =
      sheafCharacterValue G T χ x := by
  change sheafCharacterValue G T χ (G.obj.map (𝟙 T).op x) = sheafCharacterValue G T χ x
  exact congrArg (sheafCharacterValue G T χ) (G.obj.map_id_apply (Opposite.op T) x)

/-- Evaluation followed by restriction along evaluation is the identity
on the character sheaf. This holds without representability assumptions. -/
theorem sheafBidualEvaluation_triangle (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) :
    sheafBidualEvaluation (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G) ≫
      (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (sheafBidualEvaluation G).op = 𝟙 (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G) := by
  apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  exact (sheafBidualEvaluation_value G U.unop.left x
    ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G).obj.map U.unop.hom.op χ)).trans
      (sheafCharacterValue_restrict G T.unop χ U.unop x)

/-- Canonical bidual evaluation is natural in every morphism of
commutative fppf sheaves. -/
theorem sheafBidualEvaluation_natural {G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (a : G ⟶ H) :
    sheafBidualEvaluation G ≫
        (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map a.op).op =
      a ≫ sheafBidualEvaluation H := by
  apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro χ
  change sheafCharacterValue G U.unop.left
      (((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map a.op).hom.app (Opposite.op U.unop.left) χ)
        (G.obj.map U.unop.hom.op x) =
    sheafCharacterValue H U.unop.left χ (H.obj.map U.unop.hom.op (a.hom.app T x))
  exact (cartierDualSheafMap_value a U.unop.left χ _).trans
    (congrArg (sheafCharacterValue H U.unop.left χ) (a.hom.naturality_apply U.unop.hom.op x))

/-- Perfection of canonical evaluation transfers along an isomorphism
of the original commutative fppf sheaves. -/
theorem sheafBidualEvaluation_isIso_of_iso {G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : G ≅ H)
    [IsIso (sheafBidualEvaluation H)] : IsIso (sheafBidualEvaluation G) := by
  let dd : CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G) ⟶ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf H) :=
    (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map e.hom.op).op
  have hd : IsIso dd := ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso
    ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso e.op).op).isIso_hom
  have hcomp : IsIso (sheafBidualEvaluation G ≫ dd) :=
    (sheafBidualEvaluation_natural e.hom).symm ▸ inferInstanceAs
      (IsIso (e.hom ≫ sheafBidualEvaluation H))
  exact IsIso.of_isIso_comp_right (sheafBidualEvaluation G) dd

/-- A bilinear pairing is its left adjoint into the actual character
sheaf; this description is equivalent to a natural pairing on sections. -/
structure BilinearPairing (G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S) where
  leftAdjoint : G ⟶ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf H

/-- The right adjoint is the transpose of the left adjoint under
canonical evaluation, without assuming evaluation is invertible. -/
def BilinearPairing.rightAdjoint {G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : BilinearPairing G H) :
    H ⟶ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G :=
  sheafBidualEvaluation H ≫ (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map e.leftAdjoint.op

/-- The two adjoints give the same pairing on all sections. -/
theorem BilinearPairing.adjoint_value {G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : BilinearPairing G H) (T : Over S)
    (x : G.obj.obj (Opposite.op T)) (y : H.obj.obj (Opposite.op T)) :
    sheafCharacterValue G T (e.rightAdjoint.hom.app (Opposite.op T) y) x =
      sheafCharacterValue H T (e.leftAdjoint.hom.app (Opposite.op T) x) y :=
  (cartierDualSheafMap_value e.leftAdjoint T ((sheafBidualEvaluation H).hom.app (Opposite.op T) y) x).trans
    (sheafBidualEvaluation_value H T y (e.leftAdjoint.hom.app (Opposite.op T) x))

/-- A perfect pairing identifies each sheaf with the other's actual character sheaf. -/
def BilinearPairing.IsPerfect {G H : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : BilinearPairing G H) : Prop :=
  IsIso e.leftAdjoint ∧ IsIso e.rightAdjoint

/-- The canonical Cartier evaluation pairing. -/
def cartierEvaluationPairing (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) : BilinearPairing G (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G) :=
  ⟨sheafBidualEvaluation G⟩

/-- Canonical evaluation is perfect exactly when canonical bidual
evaluation is an isomorphism; its other adjoint is always the identity. -/
theorem cartierEvaluationPairing_isPerfect_iff (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) :
    (cartierEvaluationPairing G).IsPerfect ↔ IsIso (sheafBidualEvaluation G) := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    change IsIso (sheafBidualEvaluation (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G) ≫
      (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (sheafBidualEvaluation G).op)
    exact (sheafBidualEvaluation_triangle G).symm ▸ (Iso.refl (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G)).isIso_hom

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes
