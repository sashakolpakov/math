import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleDegreeCoordinates

/-! # Principal Top Degree -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopDegree

noncomputable section

/-! A principal top-form class in its original codimension degree
has the same native global value after the canonical single-degree
transport. No sign is discarded by the change of coordinates. -/
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
  (g c : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev source := Principal.MappedSingleGlobal.sourceComplex
  (TopCover.coefficients p k n X) (TopCover.form p k n X g) c

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
    (source p k n X g c) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (source p k n X g c)) (g+c))]
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
    (source p k n X g g) (g+g))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (source p k n X g g)) (g+g))]

def localChange := Principal.MappedSingleDegreeCoordinates.sourceIso
  (TopCover.coefficients p k n X) (TopCover.form p k n X g)
  c g g F W

def globalValue := Principal.PresheafCover.Comparison.comparison F W B J r s V T l t
    (source p k n X g c) (g+c) ≫
  (Principal.MappedSingleCoordinates.globalCoordinates
    (TopCover.coefficients p k n X) (TopCover.form p k n X g) c g V).hom ≫
  TopCover.globalMap p k n X Y f hp I g V hV

theorem comparison : globalValue p k n X Y f hp I g c F W B J r s V hV T l t =
    (localChange p k n X g c F W).hom ≫
      PrincipalTopGlobal.globalMap p k n X Y f hp I g F W B J r s V hV T l t := by
  have h := congrArg (fun a => a ≫ (TopCover.originalIso p k n X g V).hom ≫
      TopCover.globalMap p k n X Y f hp I g V hV)
    (Principal.MappedSingleDegreeCoordinates.comparison
      (TopCover.coefficients p k n X) (TopCover.form p k n X g)
      c g g F W B J r s V T l t)
  simpa only [globalValue, localChange, PrincipalTopGlobal.globalMap,
    Principal.MappedSingleDegreeCoordinates.targetIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc] using h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopDegree
