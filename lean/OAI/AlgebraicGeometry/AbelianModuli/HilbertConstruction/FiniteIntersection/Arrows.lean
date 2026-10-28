import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AffineIntersections

/-! # Arrows -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Arrows

noncomputable section

/-! Inclusions among finite affine intersections form a finite diagram of open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R))) [CompactSpace X.left]

theorem finiteIntersectionOpen_antitone {S T : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X} (h : S.val ⊆ T.val) :
    HilbertConstruction.Finite.AffineIntersections.finiteIntersectionOpen X T ≤ HilbertConstruction.Finite.AffineIntersections.finiteIntersectionOpen X S := by
  change (⨅ i : T.val, HilbertConstruction.Finite.AffineIntersections.finiteAffineChartOpen X i.val) ≤ ⨅ i : S.val, HilbertConstruction.Finite.AffineIntersections.finiteAffineChartOpen X i.val
  apply le_iInf
  intro i
  exact iInf_le (fun j : T.val => HilbertConstruction.Finite.AffineIntersections.finiteAffineChartOpen X j.val) ⟨i.val, h i.property⟩

def finiteIntersectionArrow {S T : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X} (h : S.val ⊆ T.val) :
    HilbertConstruction.Finite.AffineIntersections.finiteIntersectionChart X T ⟶ HilbertConstruction.Finite.AffineIntersections.finiteIntersectionChart X S :=
  Over.homMk (X.left.homOfLE (finiteIntersectionOpen_antitone X h)) (by
    change X.left.homOfLE (finiteIntersectionOpen_antitone X h) ≫
      ((HilbertConstruction.Finite.AffineIntersections.finiteIntersectionOpen X S).ι ≫ X.hom) = (HilbertConstruction.Finite.AffineIntersections.finiteIntersectionOpen X T).ι ≫ X.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

instance finiteIntersectionArrow_open {S T : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X} (h : S.val ⊆ T.val) :
    IsOpenImmersion (finiteIntersectionArrow X h).left :=
  inferInstanceAs (IsOpenImmersion (X.left.homOfLE (finiteIntersectionOpen_antitone X h)))

theorem finiteIntersectionArrow_id (S : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X) :
    finiteIntersectionArrow X (Finset.Subset.refl S.val) = 𝟙 (HilbertConstruction.Finite.AffineIntersections.finiteIntersectionChart X S) := by
  apply Over.OverMorphism.ext
  exact X.left.homOfLE_rfl (HilbertConstruction.Finite.AffineIntersections.finiteIntersectionOpen X S)

theorem finiteIntersectionArrow_comp {S T U : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X}
    (hST : S.val ⊆ T.val) (hTU : T.val ⊆ U.val) :
    finiteIntersectionArrow X hTU ≫ finiteIntersectionArrow X hST =
      finiteIntersectionArrow X (hST.trans hTU) := by
  apply Over.OverMorphism.ext
  exact X.left.homOfLE_homOfLE (finiteIntersectionOpen_antitone X hTU)
    (finiteIntersectionOpen_antitone X hST)

abbrev finiteIntersectionArrowIndex :=
  {p : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X × HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X // p.1.val ⊆ p.2.val}

instance finiteIntersectionArrowIndex_finite : Finite (finiteIntersectionArrowIndex X) := inferInstance

def finiteIntersectionSource (j : finiteIntersectionArrowIndex X) : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X := j.val.1

def finiteIntersectionTarget (j : finiteIntersectionArrowIndex X) : HilbertConstruction.Finite.AffineIntersections.finiteIntersectionIndex X := j.val.2

def finiteIntersectionDiagramArrow (j : finiteIntersectionArrowIndex X) :
    HilbertConstruction.Finite.AffineIntersections.finiteIntersectionChart X (finiteIntersectionTarget X j) ⟶
      HilbertConstruction.Finite.AffineIntersections.finiteIntersectionChart X (finiteIntersectionSource X j) := finiteIntersectionArrow X j.property

instance finiteIntersectionDiagramArrow_open (j : finiteIntersectionArrowIndex X) :
    IsOpenImmersion (finiteIntersectionDiagramArrow X j).left := finiteIntersectionArrow_open X j.property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Arrows
