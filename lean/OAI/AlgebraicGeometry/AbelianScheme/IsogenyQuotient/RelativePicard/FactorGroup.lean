import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.Factor
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfSheafRestriction

/-! # Factor Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.FactorGroup.Construction

noncomputable section

/-! The descended relative Picard map preserves the intrinsic tensor
product group law on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {X : Over S} [GrpObj X] (f : X ⟶ A.scheme) [IsMonHom f]
  {Q : Over S} [GrpObj Q]
  (q : (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme ⟶ Q) [IsMonHom q]
  (i : uliftYoneda.{u + 1}.obj Q ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj)
  (hfac : uliftYoneda.map q ≫ i = Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D f)

omit [GrpObj Q] in
theorem relativePicardFactor_natural {T U : Over S} (a : U ⟶ T) (x : T ⟶ Q) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.map a.op (i.app (op T) (ULift.up x)) =
      i.app (op U) (ULift.up (a ≫ x)) :=
  (congrArg (fun b : (uliftYoneda.{u + 1}.obj Q).obj (op T) ⟶
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.obj (op U) => b (ULift.up x)) (i.naturality a.op)).symm

include hfac in
omit [GrpObj Q] [IsMonHom q] in
theorem relativePicardFactor_value {T : Over S}
    (a : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme) :
    i.app (op T) (ULift.up (a ≫ q)) = Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f T a :=
  congrArg (fun b : uliftYoneda.{u + 1}.obj (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme ⟶
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj => b.app (op T) (ULift.up a)) hfac

include hfac in
theorem relativePicardFactor_one (T : Over S) : i.app (op T) (ULift.up (1 : T ⟶ Q)) = 1 := by
  have h := relativePicardFactor_value D f q i hfac (1 : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme)
  rw [MonObj.one_comp, map_one] at h
  exact h

variable [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

include hfac in
set_option backward.isDefEq.respectTransparency false in
theorem relativePicardFactor_mul {T : Over S} (x y : T ⟶ Q) :
    i.app (op T) (ULift.up (x * y)) = i.app (op T) (ULift.up x) * i.app (op T) (ULift.up y) := by
  obtain ⟨U, p, a, b, hpflat, hpsurj, hpfp, ha, hb⟩ := FormalGeometry.Completion.FppfPairLift.Construction.fppf_lift_pair q x y
  have : Flat p.left := hpflat
  have : Surjective p.left := hpsurj
  have : LocallyOfFinitePresentation p.left := hpfp
  apply FppfSheafRestriction.Construction.fppfSheaf_restriction_injective p (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X)
  have hm (z w : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.obj (op T)) :
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.map p.op (z * w) =
        (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.map p.op z * (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.map p.op w := by
    have h := (Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf X) p.op).map_mul z w
    simp only [Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply] at h
    exact h
  rw [hm, relativePicardFactor_natural, relativePicardFactor_natural, relativePicardFactor_natural,
    MonObj.comp_mul, ha, hb, ← MonObj.mul_comp,
    relativePicardFactor_value D f q i hfac, relativePicardFactor_value D f q i hfac,
    relativePicardFactor_value D f q i hfac, map_mul]

def relativePicardFactorHom (T : Over S) :
    (T ⟶ Q) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj.obj (op T) where
  toFun x := i.app (op T) (ULift.up x)
  map_one' := relativePicardFactor_one D f q i hfac T
  map_mul' := relativePicardFactor_mul D f q i hfac

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.FactorGroup.Construction
