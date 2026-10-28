import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopDegree
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrderedInjective

/-! # Principal Sheaf Value -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafValue

noncomputable section

/-! The original additive single-sheaf comparison has the native global
top value through its original coefficient coordinate and double lift. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem comparison_square {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {A B L R : C} {A' B' L' R' Z : D}
    (a : A ⟶ B) (b : B ⟶ R) (l : A ⟶ L) (r : L ⟶ R)
    (e : G.obj R ⟶ R') (f : G.obj L ⟶ L')
    (i : A' ≅ L') (a' : A' ⟶ B') (b' : B' ⟶ R') (r' : L' ⟶ R')
    (v : R' ⟶ Z) (ho : a ≫ b = l ≫ r)
    (hc : G.map r ≫ e = f ≫ r') (hn : a' ≫ b' = i.hom ≫ r') :
    G.map a ≫ G.map b ≫ e ≫ v = G.map l ≫ f ≫ i.inv ≫ a' ≫ b' ≫ v := by
  have hi : i.inv ≫ a' ≫ b' = r' := by
    rw [hn, Iso.inv_hom_id_assoc]
  calc
    _ = G.map (a ≫ b) ≫ e ≫ v := by simp only [G.map_comp, Category.assoc]
    _ = G.map (l ≫ r) ≫ e ≫ v := by rw [ho]
    _ = G.map l ≫ (G.map r ≫ e) ≫ v := by simp only [G.map_comp, Category.assoc]
    _ = G.map l ≫ (f ≫ r') ≫ v := by rw [hc]
    _ = G.map l ≫ f ≫ (i.inv ≫ a' ≫ b') ≫ v := by rw [hi]; simp only [Category.assoc]
    _ = _ := by simp only [Category.assoc]

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

abbrev form := TopCover.form p k n X g
abbrev sheaf := AffinePrincipal.Injective.Comparison.sheaf (form p k n X g)
abbrev coefficients : Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat ⥤
    X.left.Opensᵒᵖ ⥤ AddCommGrpCat :=
  sheafToPresheaf (Opens.grothendieckTopology X.left) AddCommGrpCat
abbrev lift := AdditiveTop.Comparison.lift
abbrev original := Principal.MappedSingleCoordinates.source (coefficients p k n X)
  (sheaf p k n X g) c

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

abbrev localCoordinates := Principal.MappedSingleCoordinates.localCoordinates
  (coefficients p k n X) (sheaf p k n X g) c g F W
abbrev globalCoordinates := Principal.MappedSingleCoordinates.globalCoordinates
  (coefficients p k n X) (sheaf p k n X g) c g V
abbrev localCoefficientIso := Principal.MappedSingleCoefficients.localCoefficientIso lift
  (coefficients p k n X) (sheaf p k n X g) g F W
abbrev globalCoefficientIso := Principal.MappedSingleCoefficients.globalCoefficientIso lift
  (coefficients p k n X) (sheaf p k n X g) g V

def input := lift.map (localCoordinates p k n X g c F W).hom ≫
  (localCoefficientIso p k n X g F W).hom ≫
  (Principal.MappedSingleCoordinates.localCoordinates (TopCover.coefficients p k n X)
    (form p k n X g) c g F W).inv

def globalValue := lift.map (globalCoordinates p k n X g c V).hom ≫
  (globalCoefficientIso p k n X g V).hom ≫
  TopCover.globalMap p k n X Y f hp I g V hV

variable
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s (original p k n X g c) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (original p k n X g c)) (g+c))]
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
    (PrincipalTopDegree.source p k n X g c) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (PrincipalTopDegree.source p k n X g c)) (g+c))]
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s
    (PrincipalTopDegree.source p k n X g g) (g+g))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (PrincipalTopDegree.source p k n X g g)) (g+g))]

omit [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s (PrincipalTopDegree.source p k n X g g) (g + g))] [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (PrincipalTopDegree.source p k n X g g)) (g + g))] in
theorem comparison :
    lift.map (Principal.PresheafCover.Comparison.comparison F W B J r s V T l t
      (original p k n X g c) (g+c)) ≫ globalValue p k n X Y f hp I g c V hV =
    input p k n X g c F W ≫
      PrincipalTopDegree.globalValue p k n X Y f hp I g c F W B J r s V hV T l t := by
  let := Principal.MappedSingleCoefficients.relative_isIso lift
    (coefficients p k n X) (sheaf p k n X g) c g F B J s
  let := Principal.MappedSingleCoefficients.ordered_isIso lift
    (coefficients p k n X) (sheaf p k n X g) c g V T t
  have ho := Principal.MappedSingleCoordinates.comparison
    (coefficients p k n X) (sheaf p k n X g) c g F W B J r s V T l t
  have hc := Principal.MappedSingleCoefficients.comparison lift
    (coefficients p k n X) (sheaf p k n X g) c g F W B J r s V T l t
  have hn := Principal.MappedSingleCoordinates.comparison
    (TopCover.coefficients p k n X) (form p k n X g) c g F W B J r s V T l t
  have h := comparison_square lift _ _ _ _ _ _ _ _ _ _
    (TopCover.globalMap p k n X Y f hp I g V hV) ho hc hn
  exact h

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] [∀ (d : ℕ) (a : Fin (d + 1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F] in
theorem input_coordinates :
    input p k n X g c F W ≫
      (Principal.MappedSingleCoordinates.localCoordinates
        (TopCover.coefficients p k n X) (form p k n X g) c g F W).hom =
    lift.map (localCoordinates p k n X g c F W).hom ≫
      (localCoefficientIso p k n X g F W).hom := by
  simp only [input, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafValue
