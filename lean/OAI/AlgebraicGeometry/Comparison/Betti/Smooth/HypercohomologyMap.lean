import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap
import OAI.AlgebraicGeometry.Comparison.Betti.OpenForms

/-! # Hypercohomology Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.HypercohomologyMap

noncomputable section

/-!
# The constructed algebraic-to-smooth hypercohomology map

Integer extension is performed on actual open-section complexes, exactly as
in the preserved algebraic hypercohomology definition. Sheafification and
derived localization are then applied to the proved cochain morphism.
This constructs a map; it does not assume or assert its invertibility.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def smoothPresheafOfComplexes : X.left.Opensᵒᵖ ⥤ CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  (Opens.map (Analytification.Base.analytificationMap X)).op ⋙ Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamPresheaf (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

def openSmoothPresheafMap : Algebraic.Sheaves.deRhamPresheafOfComplexes X ⟶ smoothPresheafOfComplexes X where
  app U := Open.SmoothForms.openSmoothCochainMap X U.unop
  naturality _ _ f := Open.SmoothForms.openSmoothCochainMap_restrict X (leOfHom f.unop)

def smoothPresheafOfComplexesInt : X.left.Opensᵒᵖ ⥤ CochainComplex (ModuleCat.{0} ℂ) ℤ :=
  smoothPresheafOfComplexes X ⋙ (ComplexShape.embeddingUpIntGE 0).extendFunctor (ModuleCat.{0} ℂ)

def openSmoothPresheafMapInt : Algebraic.Sheaves.deRhamPresheafOfComplexesInt X ⟶ smoothPresheafOfComplexesInt X :=
  Functor.whiskerRight (openSmoothPresheafMap X)
    ((ComplexShape.embeddingUpIntGE 0).extendFunctor (ModuleCat.{0} ℂ))

/-- Integer-indexed smooth-form presheaf complex on actual analytic inverse images. -/
def smoothPresheafComplexInt : CochainComplex (Sheaf.CochainPullback.ComplexPresheaves X) ℤ where
  X n := smoothPresheafOfComplexesInt X ⋙ HomologicalComplex.eval _ _ n
  d i j :=
    { app := fun U => ((smoothPresheafOfComplexesInt X).obj U).d i j
      naturality := fun _ _ f => ((smoothPresheafOfComplexesInt X).map f).comm i j }
  shape i j h := NatTrans.ext (funext (fun U =>
    ((smoothPresheafOfComplexesInt X).obj U).shape i j h))
  d_comp_d' i j k _ _ := NatTrans.ext (funext (fun U =>
    ((smoothPresheafOfComplexesInt X).obj U).d_comp_d i j k))

def presheafSmoothCochainMapInt : Algebraic.Sheaves.deRhamPresheafComplexInt X ⟶ smoothPresheafComplexInt X where
  f n :=
    { app := fun U => ((openSmoothPresheafMapInt X).app U).f n
      naturality := fun _ _ f => congrArg (fun g => g.f n) ((openSmoothPresheafMapInt X).naturality f) }
  comm' i j _ := NatTrans.ext (funext (fun U => ((openSmoothPresheafMapInt X).app U).comm i j))

def smoothSheafComplexInt : CochainComplex (Algebraic.Sheaves.ComplexSheaves X) ℤ :=
  ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (smoothPresheafComplexInt X)

/-- The integer-indexed sheaf morphism has the preserved algebraic complex as its source. -/
def algebraicToSmoothSheafMapInt : Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X ⟶ smoothSheafComplexInt X :=
  ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (presheafSmoothCochainMapInt X)

def smoothHypercohomology (n : ℕ) : ModuleCat.{1} ℂ :=
  ModuleCat.of ℂ
    ((DerivedCategory.singleFunctor (Algebraic.Sheaves.ComplexSheaves X) 0).obj (Algebraic.Sheaves.constantComplexSheaf X) ⟶
      (DerivedCategory.Q.obj (smoothSheafComplexInt X))⟦(n : ℤ)⟧)

/-- The actual map on derived-category hypercohomology, induced by the constructed sheaf morphism. -/
def algebraicToSmoothHypercohomologyMap (n : ℕ) : Algebraic.Sheaves.algebraicDeRham X n ⟶ smoothHypercohomology X n :=
  ModuleCat.ofHom
    { toFun := fun a => a ≫
        (shiftFunctor (DerivedCategory (Algebraic.Sheaves.ComplexSheaves X)) (n : ℤ)).map
          (DerivedCategory.Q.map (algebraicToSmoothSheafMapInt X))
      map_add' := by intro a b; simp only [Preadditive.add_comp]
      map_smul' := by intro c a; simp only [Linear.smul_comp, RingHom.id_apply] }

/-- The map is normalized by literal extension of the already constructed local cochain map. -/
theorem presheafSmoothCochainMapInt_app (U : X.left.Opensᵒᵖ) (i : ℤ) :
    ((presheafSmoothCochainMapInt X).f i).app U =
      (((ComplexShape.embeddingUpIntGE 0).extendFunctor (ModuleCat.{0} ℂ)).map
        (Open.SmoothForms.openSmoothCochainMap X U.unop)).f i := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.HypercohomologyMap
