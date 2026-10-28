import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RowInjection
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge

/-! # Vertical Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.VerticalEdge

noncomputable section

/-! The genuine vertical edge in a complex of complexes becomes
rowwise horizontal edges after the canonical signed regrouping. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasFiniteCoproducts A]
attribute [local instance] Rotation.total Rotation.complexTotal
  Rotation.flipZero
variable (S : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ))
  (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ))
  (u : K ⟶ S.X 0) (w : ∀ j, u.f j ≫ (S.d 0 1).f j = 0)

include w in
omit [HasFiniteCoproducts A] in
private theorem closed (j r : ℕ) :
    (u.f j).f r ≫ ((S.d 0 1).f j).f r = 0 :=
  congrArg (fun a : K.X j ⟶ (S.X 1).X j => a.f r) (w j)

def rowEdge (j : ℕ) : K.X j ⟶
    (RowCoordinates.rowFunctor (A := A)).obj ((HomologicalComplex₂.flip S).X j) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (HomologicalComplex₂.flip ((HomologicalComplex₂.flip S).X j)))
    (K.X j) (fun r => (u.f j).f r) (fun r r' _ => (u.f j).comm r r') (closed S K u w j)

def rowMap : K ⟶
    ((RowCoordinates.rowFunctor (A := A)).mapHomologicalComplex (.up ℕ)).obj
      (HomologicalComplex₂.flip S) where
  f j := rowEdge S K u w j
  comm' j j' _ := by
    apply HomologicalComplex.Hom.ext
    funext r
    change ((u.f j).f r ≫
      (HomologicalComplex₂.flip ((HomologicalComplex₂.flip S).X j)).ιTotal (.up ℕ) r 0 r rfl) ≫
      (HomologicalComplex₂.total.map
        ((HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map
          ((HomologicalComplex₂.flip S).d j j')) (.up ℕ)).f r = _
    erw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
    have hu := congrArg (fun a => a.f r) (u.comm j j')
    change (u.f j).f r ≫ ((S.X 0).d j j').f r =
      (K.d j j').f r ≫ (u.f j').f r at hu
    change ((u.f j).f r ≫ ((S.X 0).d j j').f r) ≫ _ = _
    erw [hu, Category.assoc]
    rfl

def edge : K ⟶ S.total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge S) K (fun j => u.f j) (fun j j' _ => u.comm j j') w

def map : (HomologicalComplex₂.flip K).total (.up ℕ) ⟶
    (HomologicalComplex₂.flip (S.total (.up ℕ))).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map (edge S K u w)) (.up ℕ)

def rowTotal : (HomologicalComplex₂.flip K).total (.up ℕ) ⟶
    (RowCoordinates.bicomplex S).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map (rowMap S K u w)) (.up ℕ)

private theorem nativeInjection_eq (r i j s N : ℕ) (hij : i+j=s) (hN : r+s=N) :
    RotationInjection.nativeInjection S r i j N (by omega) =
      (S.ιTotal (.up ℕ) i j s hij).f r ≫
        (HomologicalComplex₂.flip (S.total (.up ℕ))).ιTotal (.up ℕ) r s N hN := by
  subst s
  rfl

theorem left_injection (r j : ℕ) :
    (HomologicalComplex₂.flip K).ιTotal (.up ℕ) r j (r+j) rfl ≫ (VerticalEdge.map S K u w).f (r+j) =
      (u.f j).f r ≫ RotationInjection.nativeInjection S r 0 j (r+j) (by omega) := by
  dsimp only [VerticalEdge.map]
  erw [HomologicalComplex₂.ιTotal_map]
  change ((edge S K u w).f j).f r ≫ _ = _
  dsimp only [edge]
  rw [AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge_f]
  erw [nativeInjection_eq S r 0 j j (r+j) (by omega) rfl]
  exact Category.assoc _ _ _

theorem right_injection (r j : ℕ) :
    (HomologicalComplex₂.flip K).ιTotal (.up ℕ) r j (r+j) rfl ≫ (rowTotal S K u w).f (r+j) =
      (u.f j).f r ≫ RowInjection.Coordinates.injection S r 0 j (r+j) (by omega) := by
  dsimp only [rowTotal]
  erw [HomologicalComplex₂.ιTotal_map]
  change ((u.f j).f r ≫
    (HomologicalComplex₂.flip ((HomologicalComplex₂.flip S).X j)).ιTotal (.up ℕ) r 0 r rfl) ≫ _ = _
  exact Category.assoc _ _ _

theorem regroup : VerticalEdge.map S K u w ≫ RowCoordinates.regroup S = rowTotal S K u w := by
  apply HomologicalComplex.Hom.ext
  funext N
  apply HomologicalComplex₂.total.hom_ext
  intro r j hrj
  change r+j=N at hrj
  subst N
  erw [HomologicalComplex.comp_f, ← Category.assoc, left_injection,
    Category.assoc, RowInjection.Coordinates.injection_regroup, right_injection]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.VerticalEdge
