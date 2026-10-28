import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCharacterGroups
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EvaluationSymmetry

/-! # Affine Evaluation Inv -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineEvaluationInv

noncomputable section

/-!
# CartierDuality: affine coordinates of scheme-valued character evaluation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits TensorProduct
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction

namespace AffineEvaluation

/-- Compose a universal evaluation diagram along a point. -/
theorem compose_value {C : Type*} [Category* C] {T P K L Q : C}
    (v : T ⟶ K) (g : T ⟶ P) (a : P ⟶ K) (j : K ⟶ L)
    (c : P ⟶ Q) (q : T ⟶ Q) (b : Q ⟶ L)
    (hv : v = g ≫ a) (ha : a ≫ j = c ≫ b) (hg : g ≫ c = q) :
    v ≫ j = q ≫ b :=
  (congrArg (fun k => k ≫ j) hv).trans
    ((Category.assoc g a j).trans
      ((congrArg (fun k => g ≫ k) ha).trans
        ((Category.assoc g c b).symm.trans (congrArg (fun k => k ≫ b) hg))))

end AffineEvaluation

namespace Schemes

/-- Evaluating a character at a point pulls back its universal-point
value along the graph of that point. -/
theorem characterEvaluation_value_universal (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) (x : T ⟶ G.X) :
    Evaluation.Construction.CharacterEvaluation.value χ x = Limits.prod.lift (𝟙 T) x ≫ SliceCharacters.Construction.Schemes.characterValue S G T χ := by
  have h := SliceCharacters.Construction.Slices.sliceNatTrans_apply T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) χ (Over.mk (𝟙 T)) x
  have hx := SliceCharacters.Construction.Slices.starAdjunction_homEquiv_left T G.X (Over.mk (𝟙 T)) x
  exact h.trans (congrArg (fun p => p ≫ SliceCharacters.Construction.Schemes.characterValue S G T χ) hx)

/-- A point of the global multiplicative group is determined by its
integral Laurent-coordinate point and its fixed base morphism. -/
theorem multiplicativeGroupPoint_integral_ext (S : Scheme.{u}) (T : Over S)
    {f g : T ⟶ (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X}
    (h : f.left ≫ SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral S = g.left ≫ SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral S) :
    f = g := by
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · exact h
  · exact f.w.trans g.w.symm

end Schemes

variable (R B A : Type u) [CommRing R] [CommRing B] [CommRing A]
variable [Algebra R B] [HopfAlgebra R A]

/-- The tensor-product algebra map evaluating the group coordinate
at the given affine point, while keeping the test-algebra scalars fixed. -/
def affinePointTensorMap (p : A →ₐ[R] B) : B ⊗[R] A →ₐ[B] B :=
  Algebra.TensorProduct.lift (AlgHom.id B B) p (fun _ _ => Commute.all _ _)

/-- The tensor coordinate evaluation has the ordinary scalar extension
of the point as its underlying linear map. -/
theorem affinePointTensorMap_linear (p : A →ₐ[R] B) :
    (affinePointTensorMap R B A p).toLinearMap = p.toLinearMap.liftBaseChange B := by
  apply AlgebraTensorModule.ext
  intro b a
  simp [affinePointTensorMap]

/-- Tensor coordinate evaluation fixes the left scalar factor. -/
theorem affinePointTensorMap_spec_left (p : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom (affinePointTensorMap R B A p).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] A)) =
      𝟙 (Spec (CommRingCat.of B)) := by
  have h : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] A) ≫
      CommRingCat.ofHom (affinePointTensorMap R B A p).toRingHom = 𝟙 (CommRingCat.of B) := by
    ext b
    change affinePointTensorMap R B A p (b ⊗ₜ[R] 1) = b
    simp [affinePointTensorMap]
  exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h).trans (Spec.map_id _))

/-- Tensor coordinate evaluation acts by the given point on the right factor. -/
theorem affinePointTensorMap_spec_right (p : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom (affinePointTensorMap R B A p).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A).toRingHom) =
      Spec.map (CommRingCat.ofHom p.toRingHom) := by
  have h : CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A).toRingHom ≫
      CommRingCat.ofHom (affinePointTensorMap R B A p).toRingHom = CommRingCat.ofHom p.toRingHom := by
    ext a
    change affinePointTensorMap R B A p (1 ⊗ₜ[R] a) = p a
    simp [affinePointTensorMap]
  exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map h)

/-- The affine point equivalence uses the expected Spec map. -/
theorem affinePoint_symm_left (p : A →ₐ[R] B) :
    ((Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm p).left = Spec.map (CommRingCat.ofHom p.toRingHom) :=
  rfl

/-- The graph of an affine point becomes the tensor evaluation map
under the proved affine product-coordinate comparison. -/
theorem affineProductCoordinates_point (p : A →ₐ[R] B) :
    (Limits.prod.lift (𝟙 ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R))))
      ((Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm p)).left ≫ AffineProduct.Construction.affineProductCoordinates R B A =
        Spec.map (CommRingCat.ofHom (affinePointTensorMap R B A p).toRingHom) := by
  let S := Spec (CommRingCat.of R)
  let T := (Spec (CommRingCat.of B)).asOver S
  let G := Characters.Construction.affineHopfGroupScheme R A
  let x : T ⟶ G.X := (Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm p
  let g : T ⟶ T ⨯ G.X := Limits.prod.lift (𝟙 T) x
  let c := AffineProduct.Construction.Schemes.productToTensor S T G.X
  let q := Spec.map (CommRingCat.ofHom (affinePointTensorMap R B A p).toRingHom)
  let e := pullbackSpecIso R B A
  have h : g.left ≫ c.left = q ≫ e.inv := by
    apply Limits.pullback.hom_ext
    · have hl : (g.left ≫ c.left) ≫ Limits.pullback.fst T.hom G.X.hom = 𝟙 T.left := by
        exact (Category.assoc g.left c.left _).trans
          ((congrArg (fun k => g.left ≫ k) (AffineProduct.Construction.Schemes.productToTensor_fst S T G.X)).trans
            (congrArg (fun k : T ⟶ T => k.left) (Limits.prod.lift_fst (𝟙 T) x)))
      have hr : (q ≫ e.inv) ≫ Limits.pullback.fst T.hom G.X.hom = 𝟙 T.left :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun k => q ≫ k) (pullbackSpecIso_inv_fst R B A)).trans
            (affinePointTensorMap_spec_left R B A p))
      exact hl.trans hr.symm
    · have hl : (g.left ≫ c.left) ≫ Limits.pullback.snd T.hom G.X.hom = x.left := by
        exact (Category.assoc g.left c.left _).trans
          ((congrArg (fun k => g.left ≫ k) (AffineProduct.Construction.Schemes.productToTensor_snd S T G.X)).trans
            (congrArg (fun k : T ⟶ G.X => k.left) (Limits.prod.lift_snd (𝟙 T) x)))
      have hr : (q ≫ e.inv) ≫ Limits.pullback.snd T.hom G.X.hom = x.left :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun k => q ≫ k) (pullbackSpecIso_inv_snd R B A)).trans
            ((affinePointTensorMap_spec_right R B A p).trans (affinePoint_symm_left R B A p).symm))
      exact hl.trans hr.symm
  change g.left ≫ c.left ≫ e.hom = q
  exact (Category.assoc g.left c.left e.hom).symm.trans
    ((congrArg (fun k => k ≫ e.hom) h).trans
      ((Category.assoc q e.inv e.hom).trans
        ((congrArg (fun k => q ≫ k) e.inv_hom_id).trans (Category.comp_id q))))

/-- Integral Laurent coordinates of evaluating an affine character at a point. -/
def affineCharacterEvaluationRing (p : A →ₐ[R] B) (z : GroupLike B (B ⊗[R] A)) :
    Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ) →+* B :=
  (affinePointTensorMap R B A p).toRingHom.comp (LaurentNaturality.Construction.integralCharacterMap B (B ⊗[R] A) z)

/-- The Laurent generator of an evaluated character is the scalar-extended
linear evaluation of its group-like tensor. -/
theorem affineCharacterEvaluationRing_generator (p : A →ₐ[R] B) (z : GroupLike B (B ⊗[R] A)) :
    affineCharacterEvaluationRing R B A p z (MonoidAlgebra.of _ _ (Multiplicative.ofAdd 1)) =
      p.toLinearMap.liftBaseChange B z.val := by
  change affinePointTensorMap R B A p
    (LaurentNaturality.Construction.integralCharacterMap B (B ⊗[R] A) z (MonoidAlgebra.of _ _ (Multiplicative.ofAdd 1))) = _
  rw [LaurentNaturality.Construction.integralCharacterMap_generator]
  exact congrArg (fun f : B ⊗[R] A →ₗ[B] B => f z.val) (affinePointTensorMap_linear R B A p)

/-- Evaluation of the actual affine character section has precisely
the integral coordinate map defined by tensor evaluation. -/
theorem affineGroupLikeSection_evaluation_integral
    (p : A →ₐ[R] B) (z : GroupLike B (B ⊗[R] A)) :
    (Evaluation.Construction.CharacterEvaluation.value (AffineCharacterValues.Construction.affineGroupLikeSection R B A z)
      ((Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm p)).left ≫
        SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral (Spec (CommRingCat.of R)) =
      Spec.map (CommRingCat.ofHom (affineCharacterEvaluationRing R B A p z)) := by
  let S := Spec (CommRingCat.of R)
  let G := Characters.Construction.affineHopfGroupScheme R A
  let T := (Spec (CommRingCat.of B)).asOver S
  let x : T ⟶ G.X := (Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm p
  let χ := AffineCharacterValues.Construction.affineGroupLikeSection R B A z
  let v := Evaluation.Construction.CharacterEvaluation.value χ x
  let g := Limits.prod.lift (𝟙 T) x
  let a := SliceCharacters.Construction.Schemes.characterValue S G T χ
  let j := SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral S
  let c := AffineProduct.Construction.affineProductCoordinates R B A
  let q := Spec.map (CommRingCat.ofHom (affinePointTensorMap R B A p).toRingHom)
  let b := Spec.map (CommRingCat.ofHom (LaurentNaturality.Construction.integralCharacterMap B (B ⊗[R] A) z))
  have hv : v.left = g.left ≫ a.left :=
    congrArg (fun k : T ⟶ (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X => k.left)
      (Schemes.characterEvaluation_value_universal S G T χ x)
  have h := AffineEvaluation.compose_value v.left g.left a.left j c q b hv
    (AffineCharacterValues.Construction.affineGroupLikeSection_integralValue R B A z) (affineProductCoordinates_point R B A p)
  have he : Spec.map (CommRingCat.ofHom (affineCharacterEvaluationRing R B A p z)) = q ≫ b := by
    change Spec.map (CommRingCat.ofHom
      ((affinePointTensorMap R B A p).toRingHom.comp (LaurentNaturality.Construction.integralCharacterMap B (B ⊗[R] A) z))) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  exact h.trans he.symm

variable [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A]

local instance e56AffineEvaluationDualRing : CommRing (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convCommRing
local instance e56AffineEvaluationDualAlgebra : Algebra R (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convAlgebra

/-- Exchanging a point and a character under bidual evaluation gives
the same integral Laurent-coordinate map. -/
theorem affineCharacterEvaluationRing_symmetry (p : A →ₐ[R] B) (q : DualAlgebra.Construction.DualCoordinate R A →ₐ[R] B) :
    affineCharacterEvaluationRing R B A p (DualAlgebra.Construction.affineDualPointsEquivCharacters R B A q) =
      affineCharacterEvaluationRing R B (DualAlgebra.Construction.DualCoordinate R A) q
        (DualAlgebra.Construction.affineDualPointsEquivCharacters R B (DualAlgebra.Construction.DualCoordinate R A) (EvaluationSymmetry.Construction.bidualEvaluationAlgPoint R B A p)) := by
  apply LaurentNaturality.Construction.integralLaurentHom_ext
  rw [affineCharacterEvaluationRing_generator, affineCharacterEvaluationRing_generator]
  exact (EvaluationSymmetry.Construction.affineCharacterEvaluation_symmetry R B A p q).symm

/-- The actual affine Cartier pairing at an original algebra point
and a dual algebra point. -/
def affineCartierPairValue (p : A →ₐ[R] B) (q : DualAlgebra.Construction.DualCoordinate R A →ₐ[R] B) :
    (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)) ⟶
      (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (CommRingCat.of R))).X :=
  Evaluation.Construction.CharacterEvaluation.value
    (AffineCharacterValues.Construction.affineGroupLikeSection R B A (DualAlgebra.Construction.affineDualPointsEquivCharacters R B A q))
    ((Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm p)

/-- The canonical affine evaluation pairing agrees with evaluation
after passing to the coordinate bidual, as an actual multiplicative-group
point over the original affine base. -/
theorem affineCharacterEvaluation_value_symmetry (p : A →ₐ[R] B) (q : DualAlgebra.Construction.DualCoordinate R A →ₐ[R] B) :
    affineCartierPairValue R B A p q =
      affineCartierPairValue R B (DualAlgebra.Construction.DualCoordinate R A) q (EvaluationSymmetry.Construction.bidualEvaluationAlgPoint R B A p) := by
  apply Schemes.multiplicativeGroupPoint_integral_ext
    (Spec (CommRingCat.of R)) ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)))
  exact (affineGroupLikeSection_evaluation_integral R B A p _).trans
    ((congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (affineCharacterEvaluationRing_symmetry R B A p q)).trans
        (affineGroupLikeSection_evaluation_integral R B (DualAlgebra.Construction.DualCoordinate R A) q _).symm)

/-- The native group-scheme isomorphism supplied by the coordinate
bidual bialgebra equivalence. Its inverse will be identified with evaluation. -/
def coordinateBidualGroupIso :
    Characters.Construction.affineHopfGroupScheme R (DualAlgebra.Construction.DualCoordinate R (DualAlgebra.Construction.DualCoordinate R A)) ≅ Characters.Construction.affineHopfGroupScheme R A :=
  (hopfSpec (CommRingCat.of R)).mapIso
    (CommHopfAlgCat.isoMk (DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A)).op

/-- On affine points, the inverse coordinate-bidual isomorphism is
the algebra point obtained by composing with the inverse evaluation isomorphism. -/
theorem coordinateBidualGroupIso_inv_point (p : A →ₐ[R] B) :
    (Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm p ≫ (coordinateBidualGroupIso R A).inv.hom.hom =
      (Characters.Construction.affineSchemePointsEquivAlgHom R (DualAlgebra.Construction.DualCoordinate R (DualAlgebra.Construction.DualCoordinate R A)) B).symm
        (EvaluationSymmetry.Construction.bidualEvaluationAlgPoint R B A p) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom p.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A).symm.toAlgEquiv.toRingEquiv.toRingHom) =
    Spec.map (CommRingCat.ofHom
      (p.toRingHom.comp (DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A).symm.toAlgEquiv.toRingEquiv.toRingHom))
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineEvaluationInv
