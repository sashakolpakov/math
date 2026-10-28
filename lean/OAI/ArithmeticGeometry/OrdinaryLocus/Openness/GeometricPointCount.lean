import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PointDistinct
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricPointImage
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CountTopology
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication
import Mathlib.Data.Fintype.EquivFin

/-! # Geometric Point Count -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricPointCount.Construction

noncomputable section

/-! Lower semicontinuity of finite geometric-point counts for Openness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme} (A : Over S) [IsSeparated A.hom]

instance finite_geometricPoints_of_isFinite [IsFinite A.hom] (s : S) :
    Finite (DefinitionsTorsion.geometricPoint S s ⟶ A) :=
  Multiplication.Construction.finite_fieldPoints_of_isFinite A (DefinitionsTorsion.geometricPoint S s).hom

/-- The geometric fiber of the configuration scheme is nonempty exactly
when the original fiber has at least `n` geometric points. -/
theorem nonempty_geometricPointConfiguration_iff
    (s : S) [Finite (DefinitionsTorsion.geometricPoint S s ⟶ A)] (n : ℕ) :
    Nonempty (DefinitionsTorsion.geometricPoint S s ⟶ PointDistinct.Construction.pointConfiguration A n) ↔
      n ≤ Nat.card (DefinitionsTorsion.geometricPoint S s ⟶ A) := by
  have : IsReduced (DefinitionsTorsion.geometricPoint S s).left := by
    change IsReduced (Spec (.of (AlgebraicClosure (S.residueField s))))
    infer_instance
  have : Subsingleton (DefinitionsTorsion.geometricPoint S s).left := by
    change Subsingleton (Spec (.of (AlgebraicClosure (S.residueField s))))
    infer_instance
  have : Nonempty (DefinitionsTorsion.geometricPoint S s).left := by
    change Nonempty (Spec (.of (AlgebraicClosure (S.residueField s))))
    infer_instance
  rw [PointDistinct.Construction.nonempty_pointConfiguration_iff]
  constructor
  · rintro ⟨v, hv⟩
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective v hv
  · intro hn
    let : Fintype (DefinitionsTorsion.geometricPoint S s ⟶ A) := Fintype.ofFinite _
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (α := Fin n) (β := DefinitionsTorsion.geometricPoint S s ⟶ A) (by simpa using hn)
    exact ⟨e, e.injective⟩

/-- In a separated flat family locally of finite presentation with finite
geometric fibers, having at least `n` geometric points is an open condition. -/
theorem isOpen_geometricPointCard_ge
    [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [∀ s : S, Finite (DefinitionsTorsion.geometricPoint S s ⟶ A)] (n : ℕ) :
    IsOpen {s : S | n ≤ Nat.card (DefinitionsTorsion.geometricPoint S s ⟶ A)} := by
  have heq : {s : S | n ≤ Nat.card (DefinitionsTorsion.geometricPoint S s ⟶ A)} =
      {s : S | Nonempty (DefinitionsTorsion.geometricPoint S s ⟶ PointDistinct.Construction.pointConfiguration A n)} := by
    ext s
    exact (nonempty_geometricPointConfiguration_iff A s n).symm
  rw [heq]
  exact GeometricPointImage.Construction.isOpen_nonempty_geometricPoints (PointDistinct.Construction.pointConfiguration A n)

/-- The geometric-point count of a finite flat family of finite presentation
is lower semicontinuous. -/
theorem lowerSemicontinuous_finite_geometricPointCard
    [IsFinite A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom] :
    LowerSemicontinuous (fun s : S => Nat.card (DefinitionsTorsion.geometricPoint S s ⟶ A)) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro n
  simpa only [Set.preimage_ofPred_eq, Set.Ioi, Nat.succ_le_iff] using
    isOpen_geometricPointCard_ge A (n + 1)

/-- A locally constant upper bound on a finite geometric-point count is
attained on an open locus in a separated flat family of finite presentation. -/
theorem isOpen_geometricPointCard_eq_bound
    [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [∀ s : S, Finite (DefinitionsTorsion.geometricPoint S s ⟶ A)]
    (bound : S → ℕ) (hbound : IsLocallyConstant bound)
    (hle : ∀ s, Nat.card (DefinitionsTorsion.geometricPoint S s ⟶ A) ≤ bound s) :
    IsOpen {s : S | Nat.card (DefinitionsTorsion.geometricPoint S s ⟶ A) = bound s} :=
  CountTopology.Construction.isOpen_maximalCount _ bound (isOpen_geometricPointCard_ge A) hbound hle

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricPointCount.Construction
