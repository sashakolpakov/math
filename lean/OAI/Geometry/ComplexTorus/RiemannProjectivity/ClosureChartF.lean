import OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineImageAlgebraEq
import OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothChart
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ExactProjective
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart
import Mathlib.AlgebraicGeometry.Limits

/-! # Closure Chart F -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF.Constructions.ClosureAffineChart

/-! # RiemannProjectivity: the genuine affine pullback charts of the projective closure -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

variable {n : ℕ}

def scheme (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) : Scheme :=
  pullback (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i) (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S)

def toAffine (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    scheme S i ⟶ Spec (.of (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) := pullback.fst _ _

def toClosure (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    scheme S i ⟶ ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme S := pullback.snd _ _

instance toAffine_closed (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    IsClosedImmersion (toAffine S i) := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))

instance toClosure_open (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    IsOpenImmersion (toClosure S i) := inferInstanceAs (IsOpenImmersion (pullback.snd _ _))

instance isAffine (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    IsAffine (scheme S i) := OAI.AlgebraicGeometry.Foundations.Scheme.AffineClosedImmersion.affineClosedImmersion_source_isAffine (toAffine S i)

instance isReduced (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    IsReduced (scheme S i) := isReduced_of_isOpenImmersion (toClosure S i)

def over (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) : Over OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (toAffine S i ≫ OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i)

instance over_isAffine (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    IsAffine (over S i).left := inferInstanceAs (IsAffine (scheme S i))

instance over_isReduced (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    IsReduced (over S i).left := inferInstanceAs (IsReduced (scheme S i))

set_option backward.isDefEq.respectTransparency false in
def embedding (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    over S i ⟶ OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) :=
  Over.homMk (toAffine S i) rfl

instance embedding_closed (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    IsClosedImmersion (embedding S i).left := inferInstanceAs (IsClosedImmersion (toAffine S i))

theorem toClosure_over (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    toClosure S i ≫ (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver S).hom = (over S i).hom := by
  change pullback.snd _ _ ≫ (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S ≫ OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) =
    pullback.fst _ _ ≫ OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i
  rw [← Category.assoc, ← pullback.condition, Category.assoc, OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap_over]

end Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF.Constructions.ClosureAffineChart

namespace Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF.Constructions.ClosureChartCover

/-! # RiemannProjectivity: the polynomial affine charts cover the native projective closure -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure OAI.Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF.Constructions.ClosureAffineChart

variable {n : ℕ}

def projectiveCover (n : ℕ) : (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n).OpenCover where
  I₀ := Fin (n + 1)
  X i := Spec (.of (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))
  f i := OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    obtain ⟨i, hi⟩ := OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen n x
    refine ⟨i, (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).hom ⟨x, hi⟩, ?_⟩
    change ((OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).hom ≫
      (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).inv ≫ (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι) ⟨x, hi⟩ = x
    simp

def cover (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme S).OpenCover := (projectiveCover n).pullback₂ (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S)

theorem cover_f (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (i : Fin (n + 1)) :
    (cover S).f i = ClosureAffineChart.toClosure S i := rfl

set_option backward.isDefEq.respectTransparency false in
theorem smooth (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ)))
    (h : ∀ i : Fin (n + 1), Smooth (ClosureAffineChart.over S i).hom) : Smooth (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver S).hom := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{0}) (cover S)
  intro i
  rw [cover_f, ClosureAffineChart.toClosure_over]
  exact h i

end Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF.Constructions.ClosureChartCover

end

end OAI
