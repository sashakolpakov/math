import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSupportedGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFractionData

/-! # Principal Top Factor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopFactor

noncomputable section

section

/-! The actual principal top map has the original coefficient factorization
before any choice of a supported-to-bounded target map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] (a : Fin g → Γ(X.left,U.val))

abbrev opens := SupportedGlobalData.opens p k n X U
abbrev family := SupportedGlobalData.family p k n X U g a
abbrev forget := AdditiveTop.Comparison.forget p k
abbrev localComplex := PrincipalSupportedGlobal.localComplex p k n X Y f U I

theorem totalMap :
    Principal.PresheafCover.Comparison.totalMap (opens p k n X U) (family p k n X U g a)
      (TopCover.sourceMap p k n X Y f hp I g) =
    AugmentedCech.CoefficientNaturality.Total.totalMap (family p k n X U g a)
      (AdditiveTopFractionData.restrictedMap p k n X Y f hp U I g) := rfl

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] in
theorem coefficientIso (q : ℕ) :
    PrincipalSupportedGlobal.localIso p k n X Y f U I g a q =
    AugmentedCech.CoefficientTotal.homologyIso (family p k n X U g a) (forget p k)
      (AdditiveTopFractionData.target p k n X Y f U I) q := rfl

abbrev homology_map (q : ℕ) :=
  congrArg (fun z => homologyMap z q) (totalMap p k n X Y f hp U I g a).symm

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] in
theorem coefficient_inverse (q : ℕ) :
    (AugmentedCech.CoefficientTotal.homologyIso (family p k n X U g a) (forget p k)
      (AdditiveTopFractionData.target p k n X Y f U I) q).inv =
    (PrincipalSupportedGlobal.localIso p k n X Y f U I g a q).inv := rfl

end

/-! Typed intermediate groups for the original principal top-map factorization. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem combine {C : Type*} [Category C] {A B D : C}
    (a a' : A ⟶ B) (b b' : B ⟶ D) (ha : a = a') (hb : b = b') :
    a ≫ b = a' ≫ b' := by rw [ha, hb]

private theorem postcompose {C : Type*} [Category C] {A B D E : C}
    (a a' : A ⟶ B) (b b' : B ⟶ D) (v : D ⟶ E) (h : a ≫ b = a' ≫ b') :
    a ≫ b ≫ v = a' ≫ b' ≫ v := by
  simpa only [Category.assoc] using congrArg (fun x => x ≫ v) h

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] (a : Fin g → Γ(X.left,U.val))

attribute [local irreducible] HomologicalComplex.homology

abbrev sourceGroup (q : ℕ) : AddCommGrpCat.{2} :=
  ((AugmentedOrdered.CechFunctor.bicomplex (family p k n X U g a)
    (PrincipalTopCoordinates.original p k n X U g)).total (.up ℕ)).homology q

abbrev targetGroup (q : ℕ) : AddCommGrpCat.{2} :=
  ((AugmentedOrdered.CechFunctor.bicomplex (family p k n X U g a)
    (AugmentedCech.CoefficientTotal.mapped (forget p k)
      (AdditiveTopFractionData.target p k n X Y f U I))).total (.up ℕ)).homology q

abbrev outputGroup (q : ℕ) : AddCommGrpCat.{2} :=
  (forget p k).obj (((AugmentedOrdered.CechFunctor.bicomplex (family p k n X U g a)
    (AdditiveTopFractionData.target p k n X Y f U I)).total (.up ℕ)).homology q)

def first (q : ℕ) : sourceGroup p k n X U g a q ⟶ targetGroup p k n X Y f U I g a q :=
  homologyMap (AugmentedCech.CoefficientNaturality.Total.totalMap (family p k n X U g a)
    (AdditiveTopFractionData.restrictedMap p k n X Y f hp U I g)) q

def firstOriginal (q : ℕ) : sourceGroup p k n X U g a q ⟶ targetGroup p k n X Y f U I g a q :=
  homologyMap (Principal.PresheafCover.Comparison.totalMap (opens p k n X U)
    (family p k n X U g a) (TopCover.sourceMap p k n X Y f hp I g)) q

def second (q : ℕ) : targetGroup p k n X Y f U I g a q ⟶ outputGroup p k n X Y f U I g a q :=
  (AugmentedCech.CoefficientTotal.homologyIso (family p k n X U g a) (forget p k)
    (AdditiveTopFractionData.target p k n X Y f U I) q).inv

def secondOriginal (q : ℕ) : targetGroup p k n X Y f U I g a q ⟶ outputGroup p k n X Y f U I g a q :=
  (PrincipalSupportedGlobal.localIso p k n X Y f U I g a q).inv

theorem first_eq (q : ℕ) : first p k n X Y f hp U I g a q = firstOriginal p k n X Y f hp U I g a q :=
  homology_map p k n X Y f hp U I g a q

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] in
theorem second_eq (q : ℕ) : second p k n X Y f U I g a q = secondOriginal p k n X Y f U I g a q :=
  coefficient_inverse p k n X Y f U I g a q

abbrev factors (q : ℕ) := combine
  (first p k n X Y f hp U I g a q) (firstOriginal p k n X Y f hp U I g a q)
  (second p k n X Y f U I g a q) (secondOriginal p k n X Y f U I g a q)
  (first_eq p k n X Y f hp U I g a q) (second_eq p k n X Y f U I g a q)

variable (q : ℕ) {T : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
  (b : ((AugmentedOrdered.CechFunctor.bicomplex (family p k n X U g a)
    (AdditiveTopFractionData.target p k n X Y f U I)).total (.up ℕ)).homology q ⟶ T)

abbrev map := postcompose
  (first p k n X Y f hp U I g a q) (firstOriginal p k n X Y f hp U I g a q)
  (second p k n X Y f U I g a q) (secondOriginal p k n X Y f U I g a q)
  ((forget p k).map b) (factors p k n X Y f hp U I g a q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopFactor
