import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFractionGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafValue

/-! # Principal Sheaf Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafFraction

noncomputable section

/-! The original additive single-sheaf principal comparison sends a
class with the prescribed native fraction input to the same signed
bounded residue. All global maps and coefficient lifts are retained. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem postcompose_square {C : Type*} [Category C]
    {A B D E F : C} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ D)
    (d : D ⟶ E) (e : E ⟶ F) (h : a ≫ b = c ≫ d) :
    a ≫ (b ≫ e) = c ≫ (d ≫ e) := by
  rw [← Category.assoc, h, Category.assoc]

private theorem square_zsmul {A B C D : AddCommGrpCat.{2}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) (x : A) (y : C) (v : D) (m : ℤ)
    (hx : c x = m • y) (hy : d y = v) : b (a x) = m • v := by
  have h' : b (a x) = d (c x) := ConcreteCategory.congr_hom h x
  rw [hx, map_zsmul, hy] at h'
  exact h'

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
abbrev linear := CechIso.ResolutionGlobal.presheaf p k n X Y f I
abbrev source := PrincipalTopGlobal.source p k n X g

def value (c : ℕ) {μ : Type} [LinearOrder μ]
    (V : μ → X.left.Opens) (hV : iSup V = ⊤) :=
  PrincipalSheafValue.globalValue p k n X Y f hp I g c V hV ≫
    (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g)).hom

local instance tuple_preserves (d : ℕ) (z : Fin (d+1) → ULift (Fin g)) :
    PreservesLimit (Discrete.functor (family p k n X U g a ∘ z)) (opens p k n X U) :=
  AffinePrincipal.Products.preserves X.left U.val U.property (family p k n X U g a ∘ z)

variable {κ ν μ ρ : Type}
  [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (B : κ → X.left.Opens) (J : ν → X.left.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk (ULift (Fin g))
    ((opens p k n X U).obj ∘ family p k n X U g a))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → X.left.Opens) (hV : iSup V = ⊤) (T : ρ → X.left.Opens)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover
      ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (O : X.left.Opens)
  (hO : ∀ j, (opens p k n X U).obj (family p k n X U g a j) ≤ O)
  (hB : ∀ j, B j ≤ O)
  (hcover : (opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊓ O ≤
    ⨆ j, (opens p k n X U).obj (family p k n X U g a j))
  (hglobal : (opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊔ O = ⊤)
  [IsIso (RelativeCech.Refinement.homology
    ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s
    (source p k n X g) (g+g))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (source p k n X g)) (g+g))]
  [IsIso (RelativeCech.Refinement.homology
    ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s
    (linear p k n X Y f I) (g+g))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (linear p k n X Y f I)) (g+g))]

variable (c : ℕ)
  [IsIso (RelativeCech.Refinement.homology
    ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s
    (PrincipalTopDegree.source p k n X g c) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (PrincipalTopDegree.source p k n X g c)) (g+c))]

abbrev original := PrincipalSheafValue.original p k n X g c
abbrev lift := AdditiveTop.Comparison.lift
abbrev originalSource := AffinePrincipal.Injective.Comparison.source
  (opens p k n X U) (family p k n X U g a) (TopCover.form p k n X g) c

variable
  [IsIso (RelativeCech.Refinement.homology
    ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s
    (original p k n X g c) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (original p k n X g c)) (g+c))]

omit [IsIso (RelativeCech.Refinement.homology ((opens p k n X U).obj (⊤_ PrincipalFrame.Index X.left U)) B J s (source p k n X g) (g + g))] [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (source p k n X g)) (g + g))] [IsIso (RelativeCech.Refinement.homology ((opens p k n X U).obj (⊤_ PrincipalFrame.Index X.left U)) B J s (linear p k n X Y f I) (g + g))] [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (linear p k n X Y f I)) (g + g))] in
theorem comparison :
    lift.map (Principal.PresheafCover.Comparison.comparison
      (opens p k n X U) (family p k n X U g a) B J r s V T l t
      (original p k n X g c) (g+c)) ≫ value p k n X Y f hp I g c V hV =
    PrincipalSheafValue.input p k n X g c
      (opens p k n X U) (family p k n X U g a) ≫
    PrincipalFractionGlobal.globalValue p k n X Y f hp U I g a
      B J r s V hV T l t c := by
  dsimp only [value, PrincipalFractionGlobal.globalValue]
  have h := postcompose_square (C := AddCommGrpCat.{2})
    (lift.map (Principal.PresheafCover.Comparison.comparison
      (opens p k n X U) (family p k n X U g a) B J r s V T l t
      (original p k n X g c) (g+c)))
    (PrincipalSheafValue.globalValue p k n X Y f hp I g c V hV)
    (PrincipalSheafValue.input p k n X g c
      (opens p k n X U) (family p k n X U g a))
    (PrincipalTopDegree.globalValue p k n X Y f hp I g c
      (opens p k n X U) (family p k n X U g a) B J r s V hV T l t)
    (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g)).hom
    (PrincipalSheafValue.comparison p k n X Y f hp I g c
      (opens p k n X U) (family p k n X U g a) B J r s V hV T l t)
  exact h

variable (τ : Type) [LinearOrder τ]
  [Algebra (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n) (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [Algebra.Etale (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]

attribute [local irreducible] HomologicalComplex.homology

include hB τ in
theorem fraction (x : (originalSource p k n X U g a c).homology (g+c))
    (d : ℤ) (b : WittVector p k)
    (hx : PrincipalSheafValue.input p k n X g c
      (opens p k n X U) (family p k n X U g a) (ULift.up.{2,1} (ULift.up.{1,0} x)) =
      d • ModelPrincipalFraction.input p k n X Y f hp U g a c b) :
    value p k n X Y f hp I g c V hV
      (lift.map (Principal.PresheafCover.Comparison.comparison
        (opens p k n X U) (family p k n X U g a) B J r s V T l t
        (original p k n X g c) (g+c)) (ULift.up.{2,1} (ULift.up.{1,0} x))) =
    d • (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      ((⟨b⟩ : Crystalline.ExactRestriction.Coeff (B := WittVector p k)) •
        PrincipalFractionGlobal.boundedResidue p k n X Y f hp U I g a
          O hO hcover hglobal)) := by
  exact square_zsmul
    (lift.map (Principal.PresheafCover.Comparison.comparison
      (opens p k n X U) (family p k n X U g a) B J r s V T l t
      (original p k n X g c) (g+c)))
    (value p k n X Y f hp I g c V hV)
    (PrincipalSheafValue.input p k n X g c
      (opens p k n X U) (family p k n X U g a))
    (PrincipalFractionGlobal.globalValue p k n X Y f hp U I g a
      B J r s V hV T l t c)
    (comparison p k n X Y f hp U I g a B J r s V hV T l t c)
    (ULift.up.{2,1} (ULift.up.{1,0} x))
    (ModelPrincipalFraction.input p k n X Y f hp U g a c b)
    _ d hx
    (PrincipalFractionGlobal.fraction p k n X Y f hp U I g a
      B J r s V hV T l t O hO hB hcover hglobal c τ b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafFraction
