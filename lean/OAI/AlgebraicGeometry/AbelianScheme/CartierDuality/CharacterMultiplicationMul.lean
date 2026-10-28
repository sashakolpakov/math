import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupSheaf

/-! # Character Multiplication Mul -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterMultiplicationMul

noncomputable section

/-!
# CartierDuality: multiplication in character sections and native pullback characters
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.CharacterMultiplication

/-- Precomposition and a group morphism preserve pointwise products. -/
theorem prepost_mul {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {X U : C} {K L : Grp C} (p : U ⟶ X) (q : K ⟶ L) (a b : X ⟶ K.X) :
    p ≫ (a * b) ≫ q.hom.hom = (p ≫ a ≫ q.hom.hom) * (p ≫ b ≫ q.hom.hom) := by
  rw [MonObj.mul_comp, MonObj.comp_mul]

/-- Changing source and target by group isomorphisms preserves the
group law on homomorphisms into commutative group objects. -/
def homCongrMulEquiv {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    [BraidedCategory C] {G G' K K' : Grp C} [IsCommMonObj K.X] [IsCommMonObj K'.X]
    (e : G ≅ G') (d : K ≅ K') : (G ⟶ K) ≃* (G' ⟶ K') where
  toEquiv := e.homFromEquiv.trans d.homToEquiv
  map_mul' f g := by
    change (e.inv ≫ (f * g)) ≫ d.hom = ((e.inv ≫ f) ≫ d.hom) * ((e.inv ≫ g) ≫ d.hom)
    rw [MonObj.comp_mul, MonObj.mul_comp]

end Construction.CharacterMultiplication

namespace Construction.Schemes

/-- Multiplication of character sections is pointwise multiplication
of their universal-point values. -/
theorem characterValue_mul (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S)
    (χ ψ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    SliceCharacters.Construction.Schemes.characterValue S G T (χ * ψ) = SliceCharacters.Construction.Schemes.characterValue S G T χ * SliceCharacters.Construction.Schemes.characterValue S G T ψ := rfl

/-- The product-adjunction character correspondence preserves
multiplication of the underlying morphisms. -/
theorem starCharacterEquiv_mul_underlying (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S)
    (χ ψ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    (SliceCharacters.Construction.Slices.starCharacterEquiv T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) (χ * ψ)).hom.hom =
      (SliceCharacters.Construction.Slices.starCharacterEquiv T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) χ).hom.hom *
        (SliceCharacters.Construction.Slices.starCharacterEquiv T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) ψ).hom.hom := by
  let e := SliceCharacters.Construction.Slices.starPointMulEquiv T (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) ((Over.star T).obj G.X)
  have hχ := SliceCharacters.Construction.Slices.starCharacterEquiv_underlying T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) χ
  have hψ := SliceCharacters.Construction.Slices.starCharacterEquiv_underlying T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) ψ
  have hχψ := SliceCharacters.Construction.Slices.starCharacterEquiv_underlying T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) (χ * ψ)
  exact hχψ.trans ((e.map_mul (SliceCharacters.Construction.Schemes.characterValue S G T χ) (SliceCharacters.Construction.Schemes.characterValue S G T ψ)).trans
    (congrArg₂ (fun f g : (Over.star T).obj G.X ⟶
      (Over.star T).obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X => f * g) hχ.symm hψ.symm))

/-- Underlying formula for the native character correspondence, with
all changes of slice and multiplicative-group model displayed. -/
theorem testCharacterEquiv_underlying (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    (SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T χ).hom.hom =
      (SliceCharacters.Construction.Schemes.starSchemeGroup_pullbackIso S G T).inv.hom.hom ≫
        T.iteratedSliceForward.map
          (SliceCharacters.Construction.Slices.starCharacterEquiv T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) χ).hom.hom ≫
            (SliceCharacters.Construction.Schemes.starSchemeGroup_pullbackIso S (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) T).hom.hom.hom ≫
              (SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso T.hom).hom.hom.hom := by
  have h := congrArg
    (fun f : (Over.pullback T.hom).mapGrp.obj G ⟶
        (Over.pullback T.hom).mapGrp.obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) =>
      f.hom.hom ≫ (SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso T.hom).hom.hom.hom)
      (SliceCharacters.Construction.Schemes.characterSheaf_sectionsPullbackEquiv_eq S G T χ)
  exact h.trans (Category.assoc _ _ _)

/-- The actual native pullback character correspondence preserves
pointwise multiplication of characters. -/
theorem testCharacterEquiv_mul (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S)
    (χ ψ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T (χ * ψ) =
      SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T χ * SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T ψ := by
  apply Grp.hom_ext
  change (SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T (χ * ψ)).hom.hom =
    (SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T χ).hom.hom *
      (SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T ψ).hom.hom
  rw [testCharacterEquiv_underlying, testCharacterEquiv_underlying, testCharacterEquiv_underlying,
    starCharacterEquiv_mul_underlying, Functor.map_mul]
  exact CharacterMultiplication.prepost_mul (SliceCharacters.Construction.Schemes.starSchemeGroup_pullbackIso S G T).inv.hom.hom
    ((SliceCharacters.Construction.Schemes.starSchemeGroup_pullbackIso S (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) T).hom ≫
      (SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso T.hom).hom) _ _

/-- Sections of the actual character sheaf and native group-scheme
characters over a test scheme are equivalent as groups. -/
def testCharacterMulEquiv (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S) :
    (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) ≃*
      ((Over.pullback T.hom).mapGrp.obj G ⟶ CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left) where
  toEquiv := SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv S G T
  map_mul' := testCharacterEquiv_mul S G T

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterMultiplicationMul
