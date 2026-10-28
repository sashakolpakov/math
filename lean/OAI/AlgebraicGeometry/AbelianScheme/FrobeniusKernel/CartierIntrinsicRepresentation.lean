import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierFunctoriality

/-! # Cartier Intrinsic Representation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
The actual coordinate Cartier group also has CartierDuality's native character
representation, with the same pointwise evaluation. This connects the
constructed opposite kernels to CartierDuality's full commutative sheaf duality.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

variable {R : CommRingCat.{u}} {G : Grp (Over (Spec R))}

/-- Both character conventions use literal pointwise multiplication. -/
def CartierIntrinsicRepresentation.Construction.characterConventionEquiv (G : Grp (Over (Spec R))) (T : Over (Spec R)) :
    CharacterGroups.Construction.CharacterSections G T ≃* (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) G).obj.obj (op T) where
  toEquiv := Equiv.refl _
  map_mul' a b := by
    apply NatTrans.ext
    funext U
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    rfl

variable (P : CartierModel.Construction.CartierCoordinates R G)

/-- The coordinate model represents the actual commutative character sheaf
in the common universe. No choice of a smaller character type is needed. -/
def CartierModel.Construction.CartierCoordinates.representedCharacterIso :
    CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) P.dualGroup ≅ CartierDuality.CharacterGroupSheaf.Construction.Schemes.characterCommGroupSheaf (Spec R) G := by
  let e (T : (Over (Spec R))ᵒᵖ) :
      (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) P.dualGroup).obj.obj T ≃*
        (CartierDuality.CharacterGroupSheaf.Construction.Schemes.characterCommGroupSheaf (Spec R) G).obj.obj T :=
    MulEquiv.ulift.trans ((P.pointsEquiv T.unop).trans (CartierIntrinsicRepresentation.Construction.characterConventionEquiv G T.unop))
  apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
  refine NatIso.ofComponents (fun T => (e T).toCommGrpIso) ?_
  intro T U f
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨d⟩
  exact P.characterRepresentation.homEquiv_comp f.unop d

theorem CartierModel.Construction.CartierCoordinates.representedCharacterIso_apply (T : Over (Spec R)) (d : T ⟶ P.dualGroup.X) :
    P.representedCharacterIso.hom.hom.app (op T) (ULift.up d) = P.pointsEquiv T d := rfl

/-- The actual native dual represents the sheaf Cartier dual, including
its commutative group law. -/
def CartierModel.Construction.CartierCoordinates.representedCartierDualIso [IsCommMonObj G.X] :
    CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) P.dualGroup ≅ CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) G) :=
  P.representedCharacterIso ≪≫ CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSheafIso (Spec R) G

/-- The comparison retains the original character on every test scheme. -/
theorem CartierModel.Construction.CartierCoordinates.representedCartierDualIso_apply [IsCommMonObj G.X]
    (T : Over (Spec R)) (d : T ⟶ P.dualGroup.X) :
    P.representedCartierDualIso.hom.hom.app (op T) (ULift.up d) =
      CartierDuality.SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv (Spec R) G T (P.pointsEquiv T d) := rfl

/-- The represented pairing is the literal universe lift of evaluation
of the original character. -/
theorem CartierModel.Construction.CartierCoordinates.representedCartierDualIso_value [IsCommMonObj G.X]
    (T : Over (Spec R)) (d : T ⟶ P.dualGroup.X) (x : T ⟶ G.X) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) G) T
      (P.representedCartierDualIso.hom.hom.app (op T) (ULift.up d)) (ULift.up x) =
        ULift.up ((P.pointsEquiv T d).app (op (Over.mk (𝟙 T))) x) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
