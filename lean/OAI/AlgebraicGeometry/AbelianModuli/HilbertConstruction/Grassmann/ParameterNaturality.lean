import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterScheme

/-! # Parameter Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterNaturality

noncomputable section

/-! Naturality of the global Grassmannian classification under arbitrary coefficient changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
  {S : Scheme.{u}} (A B : CommRingCat.{u}) (φ : A →+* B) (f : Spec A ⟶ S)

/-- Extending the quotient coefficients is represented by precomposing the classifying scheme map. -/
theorem grassmannParameterAffinePointEquiv_naturality
    (N : Module.Grassmannian A (ν → A) (Fintype.card ι)) :
    (ParameterScheme.grassmannParameterAffinePointEquiv (ι := ι) (ν := ν) B
      (Spec.map (CommRingCat.ofHom φ) ≫ f) (HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ N)).left =
      Spec.map (CommRingCat.ofHom φ) ≫ (ParameterScheme.grassmannParameterAffinePointEquiv A f N).left := by
  rw [ParameterScheme.grassmannParameterAffinePointEquiv_left, ParameterScheme.grassmannParameterAffinePointEquiv_left,
    HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap_comp, ← Category.assoc, HilbertScheme.Presentations.Quotient.ClassifyingNaturality.Grassmannian.quotientClassifyingMap_natural, Category.assoc]
  rfl

/-- The naturality equation holds as an equality of morphisms over the chosen base scheme. -/
theorem grassmannParameter_classifying_naturality
    (N : Module.Grassmannian A (ν → A) (Fintype.card ι)) :
    ParameterScheme.grassmannParameterAffinePointEquiv (ι := ι) (ν := ν) B
      (Spec.map (CommRingCat.ofHom φ) ≫ f) (HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ N) =
    (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl :
      Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ f) ⟶ Over.mk f) ≫
        ParameterScheme.grassmannParameterAffinePointEquiv A f N :=
  Over.OverMorphism.ext (grassmannParameterAffinePointEquiv_naturality A B φ f N)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterNaturality
