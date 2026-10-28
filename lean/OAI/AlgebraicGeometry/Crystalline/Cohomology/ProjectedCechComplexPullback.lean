import OAI.AlgebraicGeometry.Crystalline.Cohomology.SmallProjectedLE
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex

/-! # Projected Cech Complex Pullback -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ProjectedCechComplexPullback.SmallProjectedCechComplexPullback

noncomputable section

/-! The common-cover description of geometric Cech pullback
commutes with the actual presheaf differential and totalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u c v
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
  {C : Type c} [Category.{v} C] [HasBinaryProducts C]
  (F : C ⥤ Y.Opens) (G : C ⥤ X.Opens) (tau : G ⟶ F ⋙ RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.preimage f)
  {ι κ : Type} (U : ι → C) (V : κ → Y.Opens)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) G]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

def targetPullback := NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u} R) F
def sourcePullback := NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u} R) G

instance target_additive : (targetPullback R F).Additive := by
  dsimp only [targetPullback]
  infer_instance
instance source_additive : (sourcePullback R G).Additive := by
  dsimp only [sourcePullback]
  infer_instance

def restriction : RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.functor R f ⋙ targetPullback R F ⟶ sourcePullback R G where
  app Q := Functor.whiskerRight (NatTrans.op tau) Q
  naturality Q Q' a := by
    apply NatTrans.ext
    funext W
    exact (a.naturality (tau.app W.unop).op).symm

variable {K : CochainComplex (RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.Presheaves R Y) ℕ}
  {L : CochainComplex (RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.Presheaves R X) ℕ}
  (b : K ⟶ ((RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.functor R f).mapHomologicalComplex (.up ℕ)).obj L)

def pairedMap : ((targetPullback R F).mapHomologicalComplex (.up ℕ)).obj K ⟶
    ((sourcePullback R G).mapHomologicalComplex (.up ℕ)).obj L :=
  ((targetPullback R F).mapHomologicalComplex (.up ℕ)).map b ≫
    ((restriction R f F G tau).mapHomologicalComplex (.up ℕ)).app L

omit [HasBinaryProducts C] in
theorem paired_component (q : ℕ) : (pairedMap R f F G tau b).f q =
    SmallProjectedLE.SmallProjectedCechPullback.transformation R f F G tau (b.f q) := rfl

def bicomplexMap := NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K ≫
  ((NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).map (pairedMap R f F G tau b) ≫
  (NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso G U L).hom

theorem comparison : bicomplexMap R f F G tau U V r b =
    RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.bicomplexMap R f V (G.obj ∘ U) r.f (SmallProjectedLE.SmallProjectedCechPullback.coverLE f F G tau U V r) b := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact SmallProjectedLE.SmallProjectedCechPullback.compatibility R f F G tau U V r (b.f q)

theorem total : HomologicalComplex₂.total.map (bicomplexMap R f F G tau U V r b) (.up ℕ) =
    HomologicalComplex₂.total.map
      (RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback.bicomplexMap R f V (G.obj ∘ U) r.f (SmallProjectedLE.SmallProjectedCechPullback.coverLE f F G tau U V r) b) (.up ℕ) :=
  congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (comparison R f F G tau U V r b)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ProjectedCechComplexPullback.SmallProjectedCechComplexPullback
