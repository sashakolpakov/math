import OAI.AlgebraicGeometry.FormalGeometry.Completion.CubeIdentity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CubicalBilinear
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear

/-! # Scheme Point Picard Pairing -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemePointPicardPairing

noncomputable section

/-! The polarization pairing is defined on points over every test scheme,
is bilinear, and is natural under pullback. Its universal class on A × A
is an actual line-bundle class, with the required axis normalizations. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u

def additivePicardPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y) →+ Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) where
  toFun x := Additive.ofMul (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map f x.toMul)
  map_zero' := (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map f).map_one
  map_add' x y := (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map f).map_mul x.toMul y.toMul

variable {K : Type u} [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]

def schemePointLineBundleClass (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (T : Over (Spec (CommRingCat.of K)))
    (a : Additive (T ⟶ A)) : Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) :=
  Additive.ofMul (Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L a.toMul)

theorem schemePointLineBundleClass_zero (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (T : Over (Spec (CommRingCat.of K))) :
    schemePointLineBundleClass A L T 0 = 0 := Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value_one A L

omit [GrpObj A] [IsCommMonObj A] in
theorem schemePointLineBundleClass_pullback (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T U : Over (Spec (CommRingCat.of K))} (j : U ⟶ T) (a : Additive (T ⟶ A)) :
    additivePicardPullback j.left (schemePointLineBundleClass A L T a) =
      schemePointLineBundleClass A L U (Additive.ofMul (j ≫ a.toMul)) :=
  Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value_pullback A L j a.toMul

variable [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

theorem schemePointLineBundleClass_cube (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (T : Over (Spec (CommRingCat.of K)))
    (a b c : Additive (T ⟶ A)) :
    schemePointLineBundleClass A L T (a + b + c) + schemePointLineBundleClass A L T a +
      schemePointLineBundleClass A L T b + schemePointLineBundleClass A L T c =
      schemePointLineBundleClass A L T (a + b) + schemePointLineBundleClass A L T (a + c) +
        schemePointLineBundleClass A L T (b + c) := by
  apply Additive.toMul.injective
  exact div_eq_one.mp (CubeIdentity.Construction.cube_class_eq_one A L a.toMul b.toMul c.toMul)

def schemePointPicardPairing (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (T : Over (Spec (CommRingCat.of K))) :
    Additive (T ⟶ A) →ₗ[ℤ] Additive (T ⟶ A) →ₗ[ℤ] Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left) :=
  CubicalBilinear.Construction.cubicalCrossBilinear (schemePointLineBundleClass A L T) (schemePointLineBundleClass_zero A L T)
    (schemePointLineBundleClass_cube A L T)

theorem schemePointPicardPairing_apply (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (T : Over (Spec (CommRingCat.of K)))
    (a b : Additive (T ⟶ A)) :
    schemePointPicardPairing A L T a b = schemePointLineBundleClass A L T (a + b) -
      schemePointLineBundleClass A L T a - schemePointLineBundleClass A L T b := rfl

theorem schemePointPicardPairing_pullback (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T U : Over (Spec (CommRingCat.of K))} (j : U ⟶ T) (a b : Additive (T ⟶ A)) :
    additivePicardPullback j.left (schemePointPicardPairing A L T a b) =
      schemePointPicardPairing A L U (Additive.ofMul (j ≫ a.toMul)) (Additive.ofMul (j ≫ b.toMul)) := by
  rw [schemePointPicardPairing_apply, map_sub, map_sub,
    schemePointLineBundleClass_pullback, schemePointLineBundleClass_pullback,
    schemePointLineBundleClass_pullback, schemePointPicardPairing_apply]
  change schemePointLineBundleClass A L U (Additive.ofMul (j ≫ (a.toMul * b.toMul))) - _ - _ = _
  rw [MonObj.comp_mul]
  rfl

theorem schemePointPicardPairing_endomorphisms (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (f g : Endomorphisms.Construction.AlgebraicEnd A) :
    schemePointPicardPairing A L A (Additive.ofMul f.toMul.hom.hom) (Additive.ofMul g.toMul.hom.hom) =
      Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing A L f g := rfl

def polarizationLineClass (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) : Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A ⊗ A).left) :=
  schemePointPicardPairing A L (A ⊗ A) (Additive.ofMul (fst A A)) (Additive.ofMul (snd A A))

theorem polarizationLineClass_pullback (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T : Over (Spec (CommRingCat.of K))} (a b : T ⟶ A) :
    additivePicardPullback (lift a b).left (polarizationLineClass A L) =
      schemePointPicardPairing A L T (Additive.ofMul a) (Additive.ofMul b) := by
  unfold polarizationLineClass
  rw [schemePointPicardPairing_pullback]
  change schemePointPicardPairing A L T (Additive.ofMul (lift a b ≫ fst A A))
    (Additive.ofMul (lift a b ≫ snd A A)) = _
  rw [lift_fst, lift_snd]

theorem polarizationLineClass_firstAxis (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    additivePicardPullback (lift (𝟙 A) (1 : A ⟶ A)).left (polarizationLineClass A L) = 0 := by
  rw [polarizationLineClass_pullback]
  exact (schemePointPicardPairing A L A (Additive.ofMul (𝟙 A))).map_zero

theorem polarizationLineClass_secondAxis (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    additivePicardPullback (lift (1 : A ⟶ A) (𝟙 A)).left (polarizationLineClass A L) = 0 := by
  rw [polarizationLineClass_pullback]
  change schemePointPicardPairing A L A 0 (Additive.ofMul (𝟙 A)) = 0
  rw [map_zero, LinearMap.zero_apply]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemePointPicardPairing
