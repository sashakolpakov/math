import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RowInjection
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge

/-! # Horizontal Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.HorizontalEdge

noncomputable section

/-! A horizontal augmentation in the original triple complex is
the outer horizontal augmentation after the canonical row regrouping. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasFiniteCoproducts A]
attribute [local instance] Rotation.total Rotation.complexTotal
  Rotation.flipZero Components.totalAdditive

variable (S : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ))
  (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ))
  (u : K ⟶ (HomologicalComplex₂.flip S).X 0)
  (w : ∀ i, u.f i ≫ (S.X i).d 0 1 = 0)

def originalEdge : K ⟶ S.total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge S) K (fun i => u.f i)
    (fun i i' _ => u.comm i i') w

def leftMap : (HomologicalComplex₂.flip K).total (.up ℕ) ⟶
    (HomologicalComplex₂.flip (S.total (.up ℕ))).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map (originalEdge S K u w)) (.up ℕ)

def rowMap := RowCoordinates.rowFunctor.map u

include w in
omit [HasFiniteCoproducts A] in
theorem augmentation_zero : u ≫ (HomologicalComplex₂.flip S).d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact w i

include w in
theorem row_cocycle (N : ℕ) :
    (rowMap S K u).f N ≫ ((RowCoordinates.bicomplex S).X N).d 0 1 = 0 := by
  have h : rowMap S K u ≫ RowCoordinates.rowFunctor.map
      ((HomologicalComplex₂.flip S).d 0 1) = 0 := by
    dsimp only [rowMap]
    rw [← Functor.map_comp, augmentation_zero S K u w, Functor.map_zero]
  exact congrArg (fun f => f.f N) h

def rightMap : (HomologicalComplex₂.flip K).total (.up ℕ) ⟶
    (RowCoordinates.bicomplex S).total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (RowCoordinates.bicomplex S))
    ((HomologicalComplex₂.flip K).total (.up ℕ)) (fun N => (rowMap S K u).f N)
    (fun N N' _ => (rowMap S K u).comm N N') (row_cocycle S K u w)

theorem left_injection (r i : ℕ) :
    (HomologicalComplex₂.flip K).ιTotal (.up ℕ) r i (r+i) rfl ≫ (leftMap S K u w).f (r+i) =
      (u.f i).f r ≫ RotationInjection.nativeInjection S r i 0 (r+i) (by omega) := by
  dsimp only [leftMap]
  erw [HomologicalComplex₂.ιTotal_map]
  change ((u.f i ≫ S.ιTotal (.up ℕ) i 0 i rfl).f r) ≫
    (HomologicalComplex₂.flip (S.total (.up ℕ))).ιTotal (.up ℕ) r i (r+i) rfl = _
  exact Category.assoc _ _ _

theorem right_injection (r i : ℕ) :
    (HomologicalComplex₂.flip K).ιTotal (.up ℕ) r i (r+i) rfl ≫ (rightMap S K u w).f (r+i) =
      (u.f i).f r ≫ RowInjection.Coordinates.injection S r i 0 (r+i) (by omega) := by
  dsimp only [rightMap]
  erw [AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge_f, ← Category.assoc]
  change ((HomologicalComplex₂.flip K).ιTotal (.up ℕ) r i (r+i) rfl ≫
    (HomologicalComplex₂.total.map
      ((HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map u) (.up ℕ)).f (r+i)) ≫ _ = _
  erw [HomologicalComplex₂.ιTotal_map]
  exact Category.assoc _ _ _

theorem comparison : leftMap S K u w ≫ RowCoordinates.regroup S = rightMap S K u w := by
  apply HomologicalComplex.Hom.ext
  funext N
  apply HomologicalComplex₂.total.hom_ext
  intro r i hri
  change r+i=N at hri
  subst N
  erw [HomologicalComplex.comp_f, ← Category.assoc, left_injection,
    Category.assoc, RowInjection.Coordinates.injection_regroup, right_injection]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.HorizontalEdge
