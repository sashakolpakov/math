import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleGlobal

/-! # Principal Top Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopGlobal

noncomputable section

/-! The actual principal comparison and the actual native top-form
map have the same global value on every genuine global cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
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
  (g : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev source := Principal.MappedSingleGlobal.sourceComplex
  (TopCover.coefficients p k n X) (TopCover.form p k n X g) g
abbrev target := AdditiveTop.Comparison.target p k n X Y f I

variable {C : Type} [Preorder C] [HasFiniteProducts C] (F : C ⥤ X.left.Opens)
  {ι κ ν μ ρ : Type}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (d : ℕ) (a : Fin (d+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (B : κ → X.left.Opens) (J : ν → X.left.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → X.left.Opens) (hV : iSup V = ⊤) (T : ρ → X.left.Opens)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
    (source p k n X g) (g+g))]
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
    (target p k n X Y f I) (g+g))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (source p k n X g)) (g+g))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (target p k n X Y f I)) (g+g))]

abbrev localIso := Principal.MappedSingleGlobal.localIso
  (TopCover.coefficients p k n X) (TopCover.form p k n X g)
  g g F W

def globalMap := Principal.PresheafCover.Comparison.comparison F W B J r s V T l t
    (source p k n X g) (g+g) ≫
  (TopCover.originalIso p k n X g V).hom ≫
    TopCover.globalMap p k n X Y f hp I g V hV

theorem comparison :
    letI := AdditiveGlobal.ResolutionFlasque.additive_edge_isIso p k n X Y f I V hV (g+g)
    globalMap p k n X Y f hp I g F W B J r s V hV T l t =
      homologyMap (Principal.PresheafCover.Comparison.totalMap F W
        (TopCover.sourceMap p k n X Y f hp I g)) (g+g) ≫
      Principal.PresheafCover.Comparison.comparison F W B J r s V T l t
        (target p k n X Y f I) (g+g) ≫
      inv (homologyMap (Presheaf.OrderedCechEdge.edge V (target p k n X Y f I)) (g+g)) := by
  let := AdditiveGlobal.ResolutionFlasque.additive_edge_isIso p k n X Y f I V hV (g+g)
  exact Principal.MappedSingleGlobal.comparison
    (TopCover.coefficients p k n X) (TopCover.form p k n X g)
    g g (target p k n X Y f I) (TopCover.sourceMap p k n X Y f hp I g)
    F W B J r s V T l t

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopGlobal
