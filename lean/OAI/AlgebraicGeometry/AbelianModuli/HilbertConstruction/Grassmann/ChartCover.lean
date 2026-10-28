import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterScheme

/-! # Chart Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartCover

noncomputable section

/-!
Every map to the global Grassmannian has an explicit open cover on which it
lifts to normalized matrix charts. The cover is the pullback of the glued atlas.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} {M : Over S}

def overMorphismPullbackLift {G U : Over S} (f : M ⟶ G) (j : U ⟶ G) :
    Over.mk (pullback.fst f.left j.left ≫ M.hom) ⟶ U :=
  Over.homMk (pullback.snd f.left j.left) (by
    rw [← j.w, ← Category.assoc, ← pullback.condition, Category.assoc, f.w]
    rfl)

def grassmannParameterOpenCover (S : Scheme.{u}) :
    (ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S).left.OpenCover :=
  (HilbertScheme.Presentations.Grassmannian.Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := ν) S).openCover

def grassmannMapChartCover (f : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S) :
    M.left.OpenCover :=
  (grassmannParameterOpenCover S).pullback₁ f.left

def grassmannMapChartOver (f : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
    (a : ι → ν) : Over S :=
  Over.mk ((grassmannMapChartCover f).f a ≫ M.hom)

def grassmannMapChartToBase (f : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
    (a : ι → ν) : grassmannMapChartOver f a ⟶ M :=
  Over.homMk ((grassmannMapChartCover f).f a) rfl

def grassmannMapChartLift (f : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
    (a : ι → ν) : grassmannMapChartOver f a ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S :=
  overMorphismPullbackLift f (HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S)

theorem grassmannMapChartLift_fac
    (f : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S) (a : ι → ν) :
    grassmannMapChartLift f a ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S =
      grassmannMapChartToBase f a ≫ f := by
  apply Over.OverMorphism.ext
  exact (grassmannParameterOpenCover (ι := ι) (ν := ν) S).pullbackHom_map f.left a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartCover
