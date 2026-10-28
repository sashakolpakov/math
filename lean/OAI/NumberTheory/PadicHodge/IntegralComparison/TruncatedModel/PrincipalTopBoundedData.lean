import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSupportedGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopFactor
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedBoundedCoordinates

/-! # Principal Top Bounded Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopBoundedData

noncomputable section

section

/-! The genuine global value of a principal top-form class is its
original supported bounded crystalline value. -/
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

abbrev localValue := AdditiveTopFractionData.map p k n X Y f hp U I g a (f ⁻¹ᵁ O)
  (Supported.OrderedCechPushforward.pulled_below f.base (opens p k n X U) (family p k n X U g a) O hO)
  (Supported.OrderedCechPushforward.pulled_cover f.base (opens p k n X U) (family p k n X U g a) O hcover)
  (SupportedRows.exactAt_succ p k n X Y f U I g a)
  (Supported.OrderedCechPushforward.pulled_global f.base (opens p k n X U) O hglobal) (g+g)

abbrev boundedMap := SupportedBoundedCoordinates.map p k n X Y f U I g a
  O hO hcover hglobal (g+g)

abbrev local_factor := PrincipalTopFactor.map p k n X Y f hp U I g a (g+g)
  (boundedMap p k n X Y f U I g a O hO hcover hglobal)

theorem global_coordinates :
    PrincipalTopGlobal.globalMap p k n X Y f hp I g
      (opens p k n X U) (family p k n X U g a) B J r s V hV T l t ≫
      (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g)).hom =
    homologyMap (Principal.PresheafCover.Comparison.totalMap (opens p k n X U)
      (family p k n X U g a) (TopCover.sourceMap p k n X Y f hp I g)) (g+g) ≫
      PrincipalSupportedGlobal.globalValue p k n X Y f U I g a B J r s V hV T l t (g+g) := by
  let G := AdditiveTop.Comparison.forget p k
  let : IsIso (RelativeCech.Refinement.homology
      ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s
      (PrincipalTopGlobal.target p k n X Y f I) (g+g)) :=
    Presheaf.CoverCoefficients.relative_isIso G (linear p k n X Y f I)
      ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s (g+g)
  let : IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
      (PrincipalTopGlobal.target p k n X Y f I)) (g+g)) :=
    Presheaf.CoverCoefficients.ordered_isIso G (linear p k n X Y f I) V T t (g+g)
  let := AdditiveGlobal.ResolutionFlasque.additive_edge_isIso p k n X Y f I V hV (g+g)
  have ht := congrArg (fun b => b ≫
      (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g)).hom)
    (PrincipalTopGlobal.comparison p k n X Y f hp I g
      (opens p k n X U) (family p k n X U g a) B J r s V hV T l t)
  simpa only [PrincipalSupportedGlobal.globalValue, Category.assoc] using ht

include hB in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] [IsIso (RelativeCech.Refinement.homology ((opens p k n X U).obj (⊤_ PrincipalFrame.Index X.left U)) B J s (source p k n X g) (g + g))] [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (source p k n X g)) (g + g))] in
theorem supported_coordinates :
    (PrincipalSupportedGlobal.localIso p k n X Y f U I g a (g+g)).hom ≫
      PrincipalSupportedGlobal.globalValue p k n X Y f U I g a B J r s V hV T l t (g+g) =
    (AdditiveTop.Comparison.forget p k).map
      (boundedMap p k n X Y f U I g a O hO hcover hglobal) := by
  have ho := PrincipalSupportedGlobal.coordinates p k n X Y f U I g a
    B J r s V hV T l t O hO hB hcover hglobal (g+g)
  have hc := SupportedBoundedCoordinates.comparison p k n X Y f U I g a
    O hO hcover hglobal (g+g)
  exact ho.trans (congrArg (fun b => (AdditiveTop.Comparison.forget p k).map b) hc)

abbrev expandedLocalValue :=
  homologyMap (Principal.PresheafCover.Comparison.totalMap (opens p k n X U)
    (family p k n X U g a) (TopCover.sourceMap p k n X Y f hp I g)) (g+g) ≫
    (PrincipalSupportedGlobal.localIso p k n X Y f U I g a (g+g)).inv ≫
    (AdditiveTop.Comparison.forget p k).map
      (boundedMap p k n X Y f U I g a O hO hcover hglobal)

theorem local_factor_coordinates :
    expandedLocalValue p k n X Y f hp U I g a O hO hcover hglobal =
      localValue p k n X Y f hp U I g a O hO hcover hglobal :=
  (local_factor p k n X Y f hp U I g a O hO hcover hglobal).symm

end

/-! The supported-to-global comparison, factored through its target
coordinate before composing the original source map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_coordinates {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (b : B ⟶ D) (c : A ⟶ D)
    (h : e.hom ≫ b = c) : b = e.inv ≫ c := by
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

attribute [local instance] tuple_preserves

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

include hB in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] [IsIso (RelativeCech.Refinement.homology ((opens p k n X U).obj (⊤_ PrincipalFrame.Index X.left U)) B J s (source p k n X g) (g + g))] [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (source p k n X g)) (g + g))] in
theorem target_coordinates :
    PrincipalSupportedGlobal.globalValue p k n X Y f U I g a B J r s V hV T l t (g+g) =
    (PrincipalSupportedGlobal.localIso p k n X Y f U I g a (g+g)).inv ≫
      (AdditiveTop.Comparison.forget p k).map
        (boundedMap p k n X Y f U I g a O hO hcover hglobal) :=
  inverse_coordinates
    (PrincipalSupportedGlobal.localIso p k n X Y f U I g a (g+g))
    (PrincipalSupportedGlobal.globalValue p k n X Y f U I g a B J r s V hV T l t (g+g))
    ((AdditiveTop.Comparison.forget p k).map
      (boundedMap p k n X Y f U I g a O hO hcover hglobal))
    (supported_coordinates p k n X Y f U I g a B J r s V hV T l t O hO hB hcover hglobal)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopBoundedData
