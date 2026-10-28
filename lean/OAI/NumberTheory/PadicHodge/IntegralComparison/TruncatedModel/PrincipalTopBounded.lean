import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopBoundedData

/-! # Principal Top Bounded -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopBounded

noncomputable section

/-! The final support-to-global composition on explicit common groups. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] PrincipalTopBoundedData.tuple_preserves

private abbrev resultGroup (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
    (n : ℕ) (Y : Over (Spec (CommRingCat.of k))) (q : ℕ) : AddCommGrpCat.{2} :=
  (AdditiveTop.Comparison.forget p k).obj
    (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
        (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
        (Witt.Crystalline.wittStructureMap p k Y) n q))

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
    ((PrincipalTopBoundedData.opens p k n X U).obj ∘ PrincipalTopBoundedData.family p k n X U g a))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → X.left.Opens) (hV : iSup V = ⊤) (T : ρ → X.left.Opens)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover
      ((PrincipalTopBoundedData.opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (O : X.left.Opens)
  (hO : ∀ j, (PrincipalTopBoundedData.opens p k n X U).obj (PrincipalTopBoundedData.family p k n X U g a j) ≤ O)
  (hB : ∀ j, B j ≤ O)
  (hcover : (PrincipalTopBoundedData.opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊓ O ≤
    ⨆ j, (PrincipalTopBoundedData.opens p k n X U).obj (PrincipalTopBoundedData.family p k n X U g a j))
  (hglobal : (PrincipalTopBoundedData.opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊔ O = ⊤)
  [IsIso (RelativeCech.Refinement.homology
    ((PrincipalTopBoundedData.opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s
    (PrincipalTopBoundedData.source p k n X g) (g+g))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (PrincipalTopBoundedData.source p k n X g)) (g+g))]
  [IsIso (RelativeCech.Refinement.homology
    ((PrincipalTopBoundedData.opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s
    (PrincipalTopBoundedData.linear p k n X Y f I) (g+g))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (PrincipalTopBoundedData.linear p k n X Y f I)) (g+g))]

section TypedCoordinates
attribute [local irreducible] HomologicalComplex.homology

def targetValue : PrincipalTopFactor.targetGroup p k n X Y f U I g a (g+g) ⟶
    resultGroup p k n Y (g+g) :=
  PrincipalSupportedGlobal.globalValue p k n X Y f U I g a B J r s V hV T l t (g+g)

def boundedValue : PrincipalTopFactor.targetGroup p k n X Y f U I g a (g+g) ⟶
    resultGroup p k n Y (g+g) :=
  (PrincipalSupportedGlobal.localIso p k n X Y f U I g a (g+g)).inv ≫
    (AdditiveTop.Comparison.forget p k).map
      (PrincipalTopBoundedData.boundedMap p k n X Y f U I g a O hO hcover hglobal)

include hB in
omit [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] [IsIso (RelativeCech.Refinement.homology ((PrincipalTopBoundedData.opens p k n X U).obj (⊤_ PrincipalFrame.Index X.left U)) B J s (PrincipalTopBoundedData.source p k n X g) (g + g))] [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (PrincipalTopBoundedData.source p k n X g)) (g + g))] in
theorem values_eq :
    targetValue p k n X Y f U I g a B J r s V hV T l t =
      boundedValue p k n X Y f U I g a O hO hcover hglobal :=
  PrincipalTopBoundedData.target_coordinates p k n X Y f U I g a B J r s V hV T l t O hO hB hcover hglobal

include hB in
abbrev value_composition :=
  congrArg (fun b : PrincipalTopFactor.targetGroup p k n X Y f U I g a (g+g) ⟶
      resultGroup p k n Y (g+g) =>
    PrincipalTopFactor.firstOriginal p k n X Y f hp U I g a (g+g) ≫ b)
    (values_eq p k n X Y f U I g a B J r s V hV T l t O hO hB hcover hglobal)

include hB in
omit [IsIso (RelativeCech.Refinement.homology ((PrincipalTopBoundedData.opens p k n X U).obj (⊤_ PrincipalFrame.Index X.left U)) B J s (PrincipalTopBoundedData.source p k n X g) (g + g))] [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (PrincipalTopBoundedData.source p k n X g)) (g + g))] in
theorem after_supported_coordinates :
    homologyMap (Principal.PresheafCover.Comparison.totalMap (PrincipalTopBoundedData.opens p k n X U)
      (PrincipalTopBoundedData.family p k n X U g a) (TopCover.sourceMap p k n X Y f hp I g)) (g+g) ≫
      PrincipalSupportedGlobal.globalValue p k n X Y f U I g a B J r s V hV T l t (g+g) =
    PrincipalTopBoundedData.expandedLocalValue p k n X Y f hp U I g a O hO hcover hglobal :=
  value_composition p k n X Y f hp U I g a B J r s V hV T l t O hO hB hcover hglobal

include hB in
omit [IsIso (RelativeCech.Refinement.homology ((PrincipalTopBoundedData.opens p k n X U).obj (⊤_ PrincipalFrame.Index X.left U)) B J s (PrincipalTopBoundedData.source p k n X g) (g + g))] [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (PrincipalTopBoundedData.source p k n X g)) (g + g))] in
theorem local_value_coordinates :
    homologyMap (Principal.PresheafCover.Comparison.totalMap (PrincipalTopBoundedData.opens p k n X U)
      (PrincipalTopBoundedData.family p k n X U g a) (TopCover.sourceMap p k n X Y f hp I g)) (g+g) ≫
      PrincipalSupportedGlobal.globalValue p k n X Y f U I g a B J r s V hV T l t (g+g) =
    PrincipalTopBoundedData.localValue p k n X Y f hp U I g a O hO hcover hglobal :=
  (after_supported_coordinates p k n X Y f hp U I g a B J r s V hV T l t O hO hB hcover hglobal).trans
    (PrincipalTopBoundedData.local_factor_coordinates p k n X Y f hp U I g a O hO hcover hglobal)

end TypedCoordinates

include hB in
theorem comparison :
    PrincipalTopGlobal.globalMap p k n X Y f hp I g
      (PrincipalTopBoundedData.opens p k n X U) (PrincipalTopBoundedData.family p k n X U g a) B J r s V hV T l t ≫
      (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g)).hom =
    PrincipalTopBoundedData.localValue p k n X Y f hp U I g a O hO hcover hglobal :=
  (PrincipalTopBoundedData.global_coordinates p k n X Y f hp U I g a B J r s V hV T l t).trans
    (local_value_coordinates p k n X Y f hp U I g a B J r s V hV T l t O hO hB hcover hglobal)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopBounded
