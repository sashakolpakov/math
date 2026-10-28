import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopFractionBounded
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CoefficientFactor

/-! # Additive Top Fraction Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFractionData

noncomputable section

/-! The actual restricted additive top-form comparison carries the
original local fraction to its signed, scalar-weighted bounded residue. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem composite_factor {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E : C} {P : D} (e : P ⟶ F.obj A)
    (a : A ⟶ B) (b : B ⟶ E) (u : P ⟶ F.obj B) (v : F.obj B ⟶ F.obj E)
    (w : P ⟶ F.obj E) (hw : w = u ≫ v) (hu : u = e ≫ F.map a) (hv : v = F.map b) :
    w = e ≫ F.map (a ≫ b) := by
  rw [hw, hu, hv, F.map_comp, Category.assoc]

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

abbrev forget := AdditiveTop.Comparison.forget p k
abbrev family := Supported.Comparison.family p k n X U g a
abbrev source := (single _ (.up ℕ) g).obj
  (PrincipalTopSingle.coefficient p k n X U g)
abbrev target := Supported.OrderedCechEdge.presheafComplex.{1,0,0,2}
  (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) Y.left.carrier
  (Supported.Comparison.opens p k n X Y f U)
  (BoundedOpen.FlasqueComplex.complex (Witt.Crystalline.wittStructureMap p k Y) n I)

def linearDeRhamMap : FractionClass.Integral.target p k n X U ⟶
    target p k n X Y f U I :=
  PrincipalSheaf.Comparison.map p k n X Y f hp U I

def linearMap : source p k n X U g ⟶ target p k n X Y f U I :=
  PrincipalTopSingle.map p k n X U g ≫
    linearDeRhamMap p k n X Y f hp U I

def restrictedMap : PrincipalTopCoordinates.original p k n X U g ⟶
    AugmentedCech.CoefficientTotal.mapped (forget p k) (target p k n X Y f U I) :=
  ((PrincipalTopCoordinates.restriction p k n X U).mapHomologicalComplex (.up ℕ)).map
    (AdditiveTop.Comparison.map p k n X Y f hp I g)

theorem deRham_factor :
    ((PrincipalTopCoordinates.restriction p k n X U).mapHomologicalComplex (.up ℕ)).map
      (AdditiveTop.Comparison.deRhamMap p k n X Y f hp I) =
    AugmentedCech.CoefficientNaturality.Total.mappedComplexMap (forget p k)
      (linearDeRhamMap p k n X Y f hp U I) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext r
  rfl

theorem factorization : restrictedMap p k n X Y f hp U I g =
    (PrincipalTopCoordinates.sourceIso p k n X U g).hom ≫
      AugmentedCech.CoefficientNaturality.Total.mappedComplexMap (forget p k)
        (linearMap p k n X Y f hp U I g) := by
  have hc := ((PrincipalTopCoordinates.restriction p k n X U).mapHomologicalComplex
    (.up ℕ)).map_comp (AdditiveTop.Comparison.topUnit p k n X g)
      (AdditiveTop.Comparison.deRhamMap p k n X Y f hp I)
  exact composite_factor
    ((PrincipalTopCoordinates.forget p k n X U).mapHomologicalComplex (.up ℕ))
    (PrincipalTopCoordinates.sourceIso p k n X U g).hom
    (PrincipalTopSingle.map p k n X U g)
    (linearDeRhamMap p k n X Y f hp U I)
    _ _ _ hc (PrincipalTopCoordinates.factorization p k n X U g)
    (deRham_factor p k n X Y f hp U I)

def inputIso (q : ℕ) := AugmentedCech.CoefficientFactor.inputIso (family p k n X U g a)
  (forget p k) (PrincipalTopCoordinates.sourceIso p k n X U g) q

variable (O : Y.left.Opens)
  (hO : ∀ i, (Supported.Comparison.opens p k n X Y f U).obj
    (Supported.Comparison.family p k n X U g a i) ≤ O)
  (hcover : (Supported.Comparison.opens p k n X Y f U).obj
    (⊤_ (PrincipalFrame.Index X.left U)) ⊓ O ≤
      ⨆ i, (Supported.Comparison.opens p k n X Y f U).obj
        (Supported.Comparison.family p k n X U g a i))
  (hrows : ∀ q r, ((BoundedSupported.Cech.bicomplex
    (Witt.Crystalline.wittStructureMap p k Y) n I
    (Supported.Comparison.opens p k n X Y f U)
    (Supported.Comparison.family p k n X U g a)).X q).ExactAt (r+1))
  (hglobal : (Supported.Comparison.opens p k n X Y f U).obj
    (⊤_ (PrincipalFrame.Index X.left U)) ⊔ O = ⊤)

abbrev toBounded (q : ℕ) := BoundedSupported.Cech.toBounded
  (Witt.Crystalline.wittStructureMap p k Y) n I
  (Supported.Comparison.opens p k n X Y f U)
  (family p k n X U g a) O hO hcover hrows hglobal q

def map (q : ℕ) := AugmentedCech.CoefficientFactor.map (family p k n X U g a) (forget p k)
  (restrictedMap p k n X Y f hp U I g) q
  (toBounded p k n X Y f U I g a O hO hcover hrows hglobal q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFractionData
