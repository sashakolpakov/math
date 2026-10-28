import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedOpenChartSmooth

/-! # Recovered Intersection Smoothness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredIntersectionSmoothness

noncomputable section

/-! The finite intersection charts of a recovered smooth ambient scheme are smooth after recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {C : Type u} [CommRing C] (X : Over (Spec (.of C))) [CompactSpace X.left]

instance originalIntersectionFunctor_affine [IsSeparated X.hom] (i : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) :
    IsAffine ((ReferenceIntersectionFunctor.originalIntersectionFunctor X).obj i).left := Finite.AffineIntersections.finiteIntersectionChart_affine X i

def finiteIntersectionChartToBase (i : Finite.AffineIntersections.finiteIntersectionIndex X) : Finite.AffineIntersections.finiteIntersectionChart X i ⟶ X :=
  Over.homMk (Finite.AffineIntersections.finiteIntersectionOpen X i).ι rfl

instance finiteIntersectionChartToBase_open (i : Finite.AffineIntersections.finiteIntersectionIndex X) :
    IsOpenImmersion (finiteIntersectionChartToBase X i).left :=
  inferInstanceAs (IsOpenImmersion (Finite.AffineIntersections.finiteIntersectionOpen X i).ι)

theorem originalIntersection_finiteType [LocallyOfFiniteType X.hom]
    (i : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) : LocallyOfFiniteType ((ReferenceIntersectionFunctor.originalIntersectionFunctor X).obj i).hom :=
  inferInstanceAs (LocallyOfFiniteType ((Finite.AffineIntersections.finiteIntersectionOpen X i).ι ≫ X.hom))

theorem originalIntersection_baseChanged_smooth
    {T : Scheme.{u}} (c : T ⟶ Spec (.of C)) [Smooth ((Over.pullback c).obj X).hom]
    (i : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) :
    Smooth (((ReferenceIntersectionFunctor.originalIntersectionFunctor X) ⋙ Over.pullback c).obj i).hom := by
  have : IsOpenImmersion (finiteIntersectionChartToBase X i).left := finiteIntersectionChartToBase_open X i
  exact Base.ChangedOpenChartSmooth.baseChangedOpenChart_smooth (finiteIntersectionChartToBase X i) c

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredIntersectionSmoothness
