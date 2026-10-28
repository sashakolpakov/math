import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelSheafComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ComplexBasisExtension

/-! # Affine Sheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AffineSheaf.Comparison

noncomputable section

/-! The glued native map has the original ordinary affine comparison
on every affine open. This follows from extension into the actual
resolution sheaves, so no new choice of affine coordinates is required. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev coefficientPresheaves := GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves
  (T := X.left.Opensᵒᵖ) (OrdinarySectionMap.Ordinary.coefficients p k n)

abbrev rawSource := ((coefficientPresheaves p k n X).mapHomologicalComplex (.up ℕ)).obj
  (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex (Truncated.Witt.Ring p k n) X)

def affineMap (U : X.left.affineOpens) :
    Presheaf.ComplexBasisExtension.sections _ X.left.carrier (rawSource p k n X) U.val ⟶
      Presheaf.ComplexBasisExtension.sections _ X.left.carrier
        (Presheaf.ComplexBasisExtension.underlying _ X.left.carrier
          (ModelSheafComparison.target p k n X Y f I)) U.val :=
  ((OrdinarySectionMap.Ordinary.coefficients p k n).mapHomologicalComplex (.up ℕ)).map
      (IntrinsicDeRham.SectionUnit.Intrinsic.rawIso (Truncated.Witt.Ring p k n) X U.val).inv ≫
    ModelSheafComparison.rawMap p k n X Y f hp I U

theorem affineMap_f (U : X.left.affineOpens) (q : ℕ) :
    (affineMap p k n X Y f hp I U).f q =
      (ModelSheafComparison.rawMap p k n X Y f hp I U).f q := by
  change (OrdinarySectionMap.Ordinary.coefficients p k n).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

def basisMap : Presheaf.ComplexBasisExtension.BasisMap
    (fun U : X.left.affineOpens => U.val) (rawSource p k n X)
    (ModelSheafComparison.target p k n X Y f I) where
  app := affineMap p k n X Y f hp I
  naturality U V h := by
    apply HomologicalComplex.Hom.ext
    funext q
    simp only [comp_f, affineMap_f]
    exact (congrArg (fun a => a.f q)
      (ModelSheafComparison.raw_naturality p k n X Y f hp I h)).symm

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] in
theorem affineBasis : Opens.IsBasis (Set.range (fun U : X.left.affineOpens => U.val)) := by
  simpa only [Subtype.range_coe] using X.left.isBasis_affineOpens

def rawGlobalMap : rawSource p k n X ⟶
    Presheaf.ComplexBasisExtension.underlying _ X.left.carrier
      (ModelSheafComparison.target p k n X Y f I) :=
  (basisMap p k n X Y f hp I).map (affineBasis p k n X)

theorem rawGlobalMap_app (U : X.left.affineOpens) (q : ℕ) :
    ((rawGlobalMap p k n X Y f hp I).f q).app (op U.val) =
      (ModelSheafComparison.rawMap p k n X Y f hp I U).f q :=
  ((basisMap p k n X Y f hp I).map_app (affineBasis p k n X) q U).trans
    (affineMap_f p k n X Y f hp I U q)

def unit : rawSource p k n X ⟶
    Presheaf.ComplexBasisExtension.underlying _ X.left.carrier
      (ModelSheafComparison.source p k n X) :=
  ((coefficientPresheaves p k n X).mapHomologicalComplex (.up ℕ)).map
    (IntrinsicDeRham.SectionUnit.Intrinsic.presheafUnit (Truncated.Witt.Ring p k n) X)

theorem factorization :
    unit p k n X ≫
      ((sheafToPresheaf (Opens.grothendieckTopology X.left) _).mapHomologicalComplex (.up ℕ)).map
        (ModelSheafComparison.map p k n X Y f hp I) =
      rawGlobalMap p k n X Y f hp I := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply TopCat.Sheaf.hom_ext ((rawSource p k n X).X q)
    ((ModelSheafComparison.target p k n X Y f I).X q)
    (Intrinsic.EtaleOpenBasis.isBasis (Truncated.Witt.Ring p k n) X)
  intro a
  rw [comp_f, NatTrans.comp_app, rawGlobalMap_app p k n X Y f hp I
    (Intrinsic.EtaleOpenBasis.affine (Truncated.Witt.Ring p k n) X a)]
  convert ModelSheafComparison.unit_map p k n X Y f hp I a q using 1 <;> rfl

theorem unit_affine (U : X.left.affineOpens) (q : ℕ) :
    (OrdinarySectionMap.Ordinary.coefficients p k n).map
      ((IntrinsicDeRham.SectionUnit.Intrinsic.unit (Truncated.Witt.Ring p k n) X U.val).f q) ≫
      ((ModelSheafComparison.map p k n X Y f hp I).f q).hom.app (op U.val) =
    (ModelSheafComparison.rawMap p k n X Y f hp I U).f q := by
  have h := congrArg (fun a => (a.f q).app (op U.val)) (factorization p k n X Y f hp I)
  rw [comp_f, NatTrans.comp_app, rawGlobalMap_app] at h
  convert h using 1 <;> rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AffineSheaf.Comparison
