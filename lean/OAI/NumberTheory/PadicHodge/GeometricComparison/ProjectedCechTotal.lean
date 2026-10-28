import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectedCechLE
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ComplexPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex

/-! # Projected Cech Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectedCechTotal.ProjectedCechComplexPullback

noncomputable section

/-! The common-cover description of geometric Cech pullback
commutes with the actual presheaf differential and totalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe v
variable (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Y)
  {C : Type} [Category.{v} C] [HasBinaryProducts C]
  (F : C ⥤ Y.Opens) (G : C ⥤ X.Opens) (tau : G ⟶ F ⋙ Cech.Image.CechImage.preimage f)
  {ι κ : Type} (U : ι → C) (V : κ → Y.Opens)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) G]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

def targetPullback := NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{0} R) F
def sourcePullback := NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{0} R) G

instance target_additive : (targetPullback R F).Additive := by
  dsimp only [targetPullback]
  infer_instance
instance source_additive : (sourcePullback R G).Additive := by
  dsimp only [sourcePullback]
  infer_instance

def restriction : Cech.Image.CechImage.functor R f ⋙ targetPullback R F ⟶ sourcePullback R G where
  app Q := Functor.whiskerRight (NatTrans.op tau) Q
  naturality Q Q' a := by
    apply NatTrans.ext
    funext W
    exact (a.naturality (tau.app W.unop).op).symm

variable {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R Y) ℕ}
  {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) ℕ}
  (b : K ⟶ ((Cech.Image.CechImage.functor R f).mapHomologicalComplex (.up ℕ)).obj L)

def pairedMap : ((targetPullback R F).mapHomologicalComplex (.up ℕ)).obj K ⟶
    ((sourcePullback R G).mapHomologicalComplex (.up ℕ)).obj L :=
  ((targetPullback R F).mapHomologicalComplex (.up ℕ)).map b ≫
    ((restriction R f F G tau).mapHomologicalComplex (.up ℕ)).app L

omit [HasBinaryProducts C] in
theorem paired_component (q : ℕ) : (pairedMap R f F G tau b).f q =
    ProjectedCechLE.ProjectedCechPullback.transformation R f F G tau (b.f q) := rfl

def bicomplexMap := CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K ≫
  ((IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).map (pairedMap R f F G tau b) ≫
  (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso G U L).hom

theorem comparison : bicomplexMap R f F G tau U V r b =
    Cech.ComplexPullback.CechPullback.bicomplexMap R f V (G.obj ∘ U) r.f (ProjectedCechLE.ProjectedCechPullback.coverLE f F G tau U V r) b := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact ProjectedCechLE.ProjectedCechPullback.compatibility R f F G tau U V r (b.f q)

theorem total : HomologicalComplex₂.total.map (bicomplexMap R f F G tau U V r b) (.up ℕ) =
    HomologicalComplex₂.total.map
      (Cech.ComplexPullback.CechPullback.bicomplexMap R f V (G.obj ∘ U) r.f (ProjectedCechLE.ProjectedCechPullback.coverLE f F G tau U V r) b) (.up ℕ) :=
  congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (comparison R f F G tau U V r b)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectedCechTotal.ProjectedCechComplexPullback
