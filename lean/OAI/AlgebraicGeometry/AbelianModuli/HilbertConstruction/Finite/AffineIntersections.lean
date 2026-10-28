import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiniteCoverModels
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affine Intersections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AffineIntersections

noncomputable section

/-! A smooth separated quasi-compact scheme has a finite collection of affine intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R)))

theorem overSpec_schemeSeparated [IsSeparated X.hom] : X.left.IsSeparated := by
  constructor
  have h : IsSeparated (X.hom ≫ terminal.from (Spec (.of R))) := inferInstance
  simpa only [terminal.comp_from] using h

variable [CompactSpace X.left]

abbrev finiteAffineCoverIndex := X.left.affineCover.finiteSubcover.I₀

def finiteAffineChartOpen (i : finiteAffineCoverIndex X) : X.left.Opens :=
  (X.left.affineCover.finiteSubcover.f i).opensRange

theorem finiteAffineChartOpen_affine (i : finiteAffineCoverIndex X) :
    IsAffineOpen (finiteAffineChartOpen X i) := by
  have : IsAffine (X.left.affineCover.finiteSubcover.X i) := by
    change IsAffine (Spec _)
    infer_instance
  exact isAffineOpen_opensRange (X.left.affineCover.finiteSubcover.f i)

theorem finiteAffineChartOpen_cover (x : X.left) : ∃ i, x ∈ finiteAffineChartOpen X i := by
  obtain ⟨i, y, hy⟩ := X.left.affineCover.finiteSubcover.exists_eq x
  exact ⟨i, y, hy⟩

abbrev finiteIntersectionIndex := {S : Finset (finiteAffineCoverIndex X) // S.Nonempty}

instance finiteIntersectionIndex_finite : Finite (finiteIntersectionIndex X) := by
  classical
  infer_instance

def finiteIntersectionOpen (S : finiteIntersectionIndex X) : X.left.Opens :=
  ⨅ i : S.val, finiteAffineChartOpen X i.val

theorem finiteIntersectionOpen_affine [IsSeparated X.hom] (S : finiteIntersectionIndex X) :
    IsAffineOpen (finiteIntersectionOpen X S) := by
  have : X.left.IsSeparated := overSpec_schemeSeparated X
  have : Nonempty S.val := by
    obtain ⟨i, hi⟩ := S.property
    exact ⟨⟨i, hi⟩⟩
  exact IsAffineOpen.iInf (fun i : S.val => finiteAffineChartOpen_affine X i.val)

abbrev finiteIntersectionChart (S : finiteIntersectionIndex X) : Over (Spec (.of R)) :=
  Over.mk ((finiteIntersectionOpen X S).ι ≫ X.hom)

instance finiteIntersectionChart_affine [IsSeparated X.hom] (S : finiteIntersectionIndex X) :
    IsAffine (finiteIntersectionChart X S).left := finiteIntersectionOpen_affine X S

instance finiteIntersectionChart_smooth [Smooth X.hom] (S : finiteIntersectionIndex X) :
    Smooth (finiteIntersectionChart X S).hom :=
  inferInstanceAs (Smooth ((finiteIntersectionOpen X S).ι ≫ X.hom))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AffineIntersections
