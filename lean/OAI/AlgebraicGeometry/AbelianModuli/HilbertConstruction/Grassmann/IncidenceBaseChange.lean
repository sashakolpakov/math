import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PairChartPullback

/-! # Incidence Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann

noncomputable section

/-! The glued incidence ideal commutes with arbitrary parameter base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M T : Over S}
variable {q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S}
variable {k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S}

theorem PairChartCover.GrassmannPairChartCover.incidenceIdeal_pullback (D : PairChartCover.GrassmannPairChartCover q k)
    (F : Matrix μ ν Γ(M.left, ⊤)) (f : T ⟶ M) :
    (D.incidenceIdeal F).comap f.left =
      (D.pullback f).incidenceIdeal (F.map f.left.appTop.hom) := by
  apply ClosedFamily.OpenEquality.ideal_eq_of_open_cover (D.pullback f).cover
  intro i
  change D.cover.I₀ at i
  let l := PairChartPullback.overOpenCoverPullbackProjection f D.cover i
  have hl : l.left ≫ D.cover.f i = ((D.pullback f).cover.f i) ≫ f.left :=
    congrArg Over.Hom.left (PairChartPullback.overOpenCoverPullbackProjection_fac f D.cover i)
  refine ((D.incidenceIdeal F).comap_comp ((D.cover.pullback₁ f.left).f i) f.left).symm.trans ?_
  refine (congrArg (fun h => (D.incidenceIdeal F).comap h) hl.symm).trans ?_
  refine ((D.incidenceIdeal F).comap_comp l.left (D.cover.f i)).trans ?_
  refine (congrArg (fun I : (D.cover.X i).IdealSheafData => I.comap l.left)
    (D.incidenceIdeal_comap F i)).trans ?_
  refine Eq.trans ?_ ((D.pullback f).incidenceIdeal_comap (F.map f.left.appTop.hom) i).symm
  change (ChartLoci.grassmannChartIncidenceIdeal (D.sourceColumns i) (D.targetColumns i)
    (D.sourceLift i) (D.targetLift i)
      (F.map (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom)).comap l.left =
    ChartLoci.grassmannChartIncidenceIdeal (D.sourceColumns i) (D.targetColumns i)
      (l ≫ D.sourceLift i) (l ≫ D.targetLift i)
        ((F.map f.left.appTop.hom).map
          (Embedded.FamilyOpenCover.overOpenCoverMap T (D.pullback f).cover i).left.appTop.hom)
  rw [ChartLoci.grassmannChartIncidenceIdeal_comap]
  have hF : (F.map (Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom).map l.left.appTop.hom =
      (F.map f.left.appTop.hom).map
        (Embedded.FamilyOpenCover.overOpenCoverMap T (D.pullback f).cover i).left.appTop.hom := by
    change F.map (l ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D.cover i).left.appTop.hom =
      F.map (Embedded.FamilyOpenCover.overOpenCoverMap T (D.pullback f).cover i ≫ f).left.appTop.hom
    exact congrArg (fun h => F.map h.left.appTop.hom)
      (PairChartPullback.overOpenCoverPullbackProjection_fac f D.cover i)
  rw [hF]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann
