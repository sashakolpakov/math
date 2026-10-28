import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeCubeClasses
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalGeometricTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # Reduced Local Cube -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalCube.Geometric

noncomputable section

/-! The cube identity for the original normalized line over a reduced
local base. It follows from the geometric cube theorem on every actual
fiber and the proved projective frame-equation triviality criterion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

universe u
variable {S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
    [IsLocallyNoetherian S] [IsReduced S] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

def cubeProduct : Over S := (A.scheme ⊗ A.scheme) ⊗ A.scheme
def cubeFirst : (cubeProduct A) ⟶ A.scheme := fst (A.scheme ⊗ A.scheme) A.scheme ≫ fst A.scheme A.scheme
def cubeSecond : (cubeProduct A) ⟶ A.scheme := fst (A.scheme ⊗ A.scheme) A.scheme ≫ snd A.scheme A.scheme
def cubeThird : (cubeProduct A) ⟶ A.scheme := snd (A.scheme ⊗ A.scheme) A.scheme

local instance cubeProduct_group : GrpObj (cubeProduct A) :=
  inferInstanceAs (GrpObj ((A.scheme ⊗ A.scheme) ⊗ A.scheme))
local instance cubeFirst_group : IsMonHom (cubeFirst A) :=
  inferInstanceAs (IsMonHom (fst (A.scheme ⊗ A.scheme) A.scheme ≫ fst A.scheme A.scheme))
local instance cubeSecond_group : IsMonHom (cubeSecond A) :=
  inferInstanceAs (IsMonHom (fst (A.scheme ⊗ A.scheme) A.scheme ≫ snd A.scheme A.scheme))
local instance cubeThird_group : IsMonHom (cubeThird A) :=
  inferInstanceAs (IsMonHom (snd (A.scheme ⊗ A.scheme) A.scheme))

local instance cubePair_proper : IsProper (A.scheme ⊗ A.scheme).hom :=
  inferInstanceAs (IsProper (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom))
local instance cubePair_smooth : Smooth (A.scheme ⊗ A.scheme).hom :=
  inferInstanceAs (Smooth (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom))
local instance cubePair_connected : GeometricallyConnected (A.scheme ⊗ A.scheme).hom :=
  GeometricallyConnected.comp (pullback.fst A.scheme.hom A.scheme.hom) A.scheme.hom
local instance cubeProduct_proper : IsProper (cubeProduct A).hom :=
  inferInstanceAs (IsProper (pullback.fst (A.scheme ⊗ A.scheme).hom A.scheme.hom ≫ (A.scheme ⊗ A.scheme).hom))
local instance cubeProduct_smooth : Smooth (cubeProduct A).hom :=
  inferInstanceAs (Smooth (pullback.fst (A.scheme ⊗ A.scheme).hom A.scheme.hom ≫ (A.scheme ⊗ A.scheme).hom))
local instance cubeProduct_connected : GeometricallyConnected (cubeProduct A).hom :=
  GeometricallyConnected.comp (pullback.fst (A.scheme ⊗ A.scheme).hom A.scheme.hom)
    (A.scheme ⊗ A.scheme).hom

include P in
theorem reducedLocal_universal_cube :
    RelativeCubeClasses.Geometric.relativeCubeClass (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
      (cubeFirst A) (cubeSecond A) (cubeThird A) = 1 := by
  let M := RelativeDifferenceBundle.Geometric.identityNormalizedLine A L
  let q := RelativeCubeClasses.Geometric.relativeCubeClass (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) (cubeFirst A) (cubeSecond A) (cubeThird A)
  let C : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (cubeProduct A).left := q.out
  have hC : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C = q := Quotient.out_eq _
  let s := (1 : Over.mk (𝟙 S) ⟶ (cubeProduct A)).left
  have hs : s ≫ (cubeProduct A).hom = 𝟙 S := (1 : Over.mk (𝟙 S) ⟶ (cubeProduct A)).w
  have haxis : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback s (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C) = 1 := by
    rw [hC]
    change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (1 : Over.mk (𝟙 S) ⟶ (cubeProduct A)).left
      (RelativeCubeClasses.Geometric.relativeCubeClass (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) (cubeFirst A) (cubeSecond A) (cubeThird A)) = 1
    rw [RelativeCubeClasses.Geometric.relativeCubeClass_pullback]
    have h₁ : (1 : Over.mk (𝟙 S) ⟶ (cubeProduct A)) ≫ (cubeFirst A) = 1 := by
      exact MonObj.one_comp (cubeFirst A)
    have h₂ : (1 : Over.mk (𝟙 S) ⟶ (cubeProduct A)) ≫ (cubeSecond A) = 1 := by
      exact MonObj.one_comp (cubeSecond A)
    have h₃ : (1 : Over.mk (𝟙 S) ⟶ (cubeProduct A)) ≫ (cubeThird A) = 1 := MonObj.one_comp _
    rw [h₁, h₂, h₃]
    simp only [RelativeCubeClasses.Geometric.relativeCubeClass, M, RelativeCubeClasses.Geometric.identityNormalizedLine_one_class, mul_one, div_one]
  let r : (Scheme.Modules.pullback s).obj C.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S :=
    Classical.choice (Quotient.exact haxis)
  let cubePresentation : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (cubeProduct A) := (P.product P).product P
  obtain ⟨e⟩ := ReducedLocalGeometricTriviality.Geometric.reducedLocal_line_trivial_of_geometric_fibers
    (X := cubeProduct A) cubePresentation s hs C r (by
    intro y
    let b := S.fromSpecResidueField y
    let k := S.residueField y
    let c := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
    change Nonempty
      (((C.pullback ((cubeProduct A).hom.fiberι y)).pullback
        (pullback.fst ((cubeProduct A).hom.fiberToSpecResidueField y) c)).sheaf ≅
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial (pullback ((cubeProduct A).hom.fiberToSpecResidueField y) c)).sheaf)
    apply @Quotient.exact _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.isoSetoid _)
      ((C.pullback ((cubeProduct A).hom.fiberι y)).pullback
        (pullback.fst ((cubeProduct A).hom.fiberToSpecResidueField y) c)) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial _)
    change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst ((cubeProduct A).hom.fiberToSpecResidueField y) c)
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback ((cubeProduct A).hom.fiberι y) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C)) = 1
    rw [hC]
    change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst ((Over.pullback b).obj (cubeProduct A)).hom c)
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst (cubeProduct A).hom b)
        (RelativeCubeClasses.Geometric.relativeCubeClass (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) (cubeFirst A) (cubeSecond A) (cubeThird A))) = 1
    rw [RelativeCubeClasses.Geometric.relativeCubeClass_baseChange, RelativeCubeClasses.Geometric.relativeCubeClass_baseChange]
    exact RelativeCubeClasses.Geometric.relativeCubeClass_eq_one_overField ((A.pullback b).pullback c) _ _ _ _)
  exact hC.symm.trans (Quotient.sound ⟨e⟩)

include P in
theorem reducedLocal_cube {U : Over S} (a b c : U ⟶ A.scheme) :
    RelativeCubeClasses.Geometric.relativeCubeClass (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) a b c = 1 := by
  let j : U ⟶ (cubeProduct A) := lift (lift a b) c
  have h := congrArg (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback j.left) (reducedLocal_universal_cube A P L)
  rw [map_one, RelativeCubeClasses.Geometric.relativeCubeClass_pullback] at h
  have h₁ : j ≫ cubeFirst A = a := by
    change lift (lift a b) c ≫ (fst (A.scheme ⊗ A.scheme) A.scheme ≫ fst A.scheme A.scheme) = a
    rw [← Category.assoc, lift_fst, lift_fst]
  have h₂ : j ≫ cubeSecond A = b := by
    change lift (lift a b) c ≫ (fst (A.scheme ⊗ A.scheme) A.scheme ≫ snd A.scheme A.scheme) = b
    rw [← Category.assoc, lift_fst, lift_snd]
  have h₃ : j ≫ cubeThird A = c := lift_snd (lift a b) c
  rw [h₁, h₂, h₃] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalCube.Geometric
