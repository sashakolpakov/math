import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopBounded
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelPrincipalFraction

/-! # Principal Fraction Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFractionGlobal

noncomputable section

/-! The genuine principal-to-global top map carries the original
single-degree fraction to its signed bounded residue. -/
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
abbrev linear := CechIso.ResolutionGlobal.presheaf p k n X Y f I
abbrev source := PrincipalTopGlobal.source p k n X g

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

def globalValue := PrincipalTopDegree.globalValue p k n X Y f hp I g c
    (opens p k n X U) (family p k n X U g a) B J r s V hV T l t ≫
  (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g)).hom

include hB in
theorem comparison :
    globalValue p k n X Y f hp U I g a B J r s V hV T l t c =
    (PrincipalTopDegree.localChange p k n X g c
      (opens p k n X U) (family p k n X U g a)).hom ≫
    PrincipalTopBoundedData.localValue p k n X Y f hp U I g a O hO hcover hglobal := by
  dsimp only [globalValue]
  rw [PrincipalTopDegree.comparison, Category.assoc,
    PrincipalTopBounded.comparison p k n X Y f hp U I g a
      B J r s V hV T l t O hO hB hcover hglobal]

abbrev boundedResidue := SupportedResidue.residue p k n X Y f hp U I g a
  (f ⁻¹ᵁ O)
  (Supported.OrderedCechPushforward.pulled_below
    (SupportedGlobalData.baseMap p k n X Y f) (opens p k n X U)
    (family p k n X U g a) O hO)
  (Supported.OrderedCechPushforward.pulled_cover
    (SupportedGlobalData.baseMap p k n X Y f) (opens p k n X U)
    (family p k n X U g a) O hcover)
  (SupportedRows.exactAt_succ p k n X Y f U I g a)
  (Supported.OrderedCechPushforward.pulled_global
    (SupportedGlobalData.baseMap p k n X Y f) (opens p k n X U) O hglobal)

variable (τ : Type) [LinearOrder τ]
  [Algebra (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n) (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [Algebra.Etale (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]

include hB τ in
theorem fraction (b : WittVector p k) :
    globalValue p k n X Y f hp U I g a B J r s V hV T l t c
      (ModelPrincipalFraction.input p k n X Y f hp U g a c b) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      ((⟨b⟩ : Crystalline.ExactRestriction.Coeff (B := WittVector p k)) •
        boundedResidue p k n X Y f hp U I g a O hO hcover hglobal) := by
  have h := ConcreteCategory.congr_hom
    (comparison p k n X Y f hp U I g a B J r s V hV T l t O hO hB hcover hglobal c)
    (ModelPrincipalFraction.input p k n X Y f hp U g a c b)
  change globalValue p k n X Y f hp U I g a B J r s V hV T l t c _ =
    PrincipalTopBoundedData.localValue p k n X Y f hp U I g a O hO hcover hglobal
      ((PrincipalTopDegree.localChange p k n X g c
        (opens p k n X U) (family p k n X U g a)).hom _) at h
  rw [ModelPrincipalFraction.degree_input] at h
  exact h.trans (AdditiveTopFraction.fraction p k n X Y f hp U I g a
    (f ⁻¹ᵁ O)
    (Supported.OrderedCechPushforward.pulled_below
      (SupportedGlobalData.baseMap p k n X Y f) (opens p k n X U)
      (family p k n X U g a) O hO)
    (Supported.OrderedCechPushforward.pulled_cover
      (SupportedGlobalData.baseMap p k n X Y f) (opens p k n X U)
      (family p k n X U g a) O hcover)
    (SupportedRows.exactAt_succ p k n X Y f U I g a)
    (Supported.OrderedCechPushforward.pulled_global
      (SupportedGlobalData.baseMap p k n X Y f) (opens p k n X U) O hglobal) τ b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFractionGlobal
