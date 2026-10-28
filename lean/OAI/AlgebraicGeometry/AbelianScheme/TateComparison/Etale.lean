import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricExt
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.Unramified.Field

/-! # Etale -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Etale

noncomputable section

/-! Reducedness and geometric-point lifting for the actual etale cover
used to descend the local trace maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem etale_field_source_reduced {k : Type} [Field k] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (.of k)) [Etale p] : IsReduced Y := by
  have hred (i : Y.affineCover.I₀) : IsReduced (Y.affineCover.X i) := by
    let R := Γ(Y.affineCover.X i, ⊤)
    let pi := Y.affineCover.f i ≫ p
    have : Etale pi := inferInstanceAs (Etale (Y.affineCover.f i ≫ p))
    let α : k →+* R := pi.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
    have hi : Function.Surjective (Scheme.ΓSpecIso (.of k)).inv.hom := by
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2
    have hα : α.FormallyUnramified := RingHom.FormallyUnramified.comp
      (RingHom.FormallyUnramified.of_surjective hi)
      (HasRingHomProperty.appTop (P := @FormallyUnramified) pi inferInstance)
    let : Algebra k R := α.toAlgebra
    have : Algebra.FormallyUnramified k R := hα
    have hfinite : α.FiniteType :=
      (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) pi inferInstance).comp
        (RingHom.FiniteType.of_surjective _ hi)
    have : Algebra.FiniteType k R := (RingHom.finiteType_algebraMap).mp hfinite
    have : _root_.IsReduced R := Algebra.FormallyUnramified.isReduced_of_field k R
    exact isReduced_of_isAffine_isReduced (Y.affineCover.X i)
  let := hred
  exact IsReduced.of_openCover Y Y.affineCover

theorem etale_geometricallyReduced {X Y : Scheme.{0}} (p : X ⟶ Y)
    [Etale p] : GeometricallyReduced p := by
  constructor
  intro k _ y Z fst snd hcart
  have : Etale snd := MorphismProperty.of_isPullback hcart inferInstance
  exact etale_field_source_reduced snd

theorem etale_source_reduced {X Y : Scheme.{0}} (p : X ⟶ Y)
    [Etale p] [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced X := by
  have := etale_geometricallyReduced p
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian p

/-- Surjectivity and etaleness give a lift over the same algebraically
closed field, rather than requiring an unspecified field extension. -/
theorem etale_surjective_geometric_lift {B : Scheme.{0}} {X Y : Over B}
    (p : X ⟶ Y) [Etale p.left] [Surjective p.left]
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ B) (x : Over.mk b ⟶ Y) :
    ∃ a : Over.mk b ⟶ X, a ≫ p = x := by
  let s : pullback p.left x.left ⟶ Spec (.of k) := pullback.snd p.left x.left
  have : Etale s := inferInstanceAs (Etale (pullback.snd p.left x.left))
  have : Surjective s := inferInstanceAs (Surjective (pullback.snd p.left x.left))
  have : JacobsonSpace (pullback p.left x.left : Scheme) := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨z₀, _⟩ := s.surjective (default : Spec (.of k))
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨z₀, trivial⟩
    isOpen_univ.isLocallyClosed
  let a₀ := pointOfClosedPoint s z hz
  have ha : a₀ ≫ s = 𝟙 _ := pointOfClosedPoint_comp s z hz
  let a : Over.mk b ⟶ X := Over.homMk (a₀ ≫ pullback.fst p.left x.left) (by
    calc
      _ = a₀ ≫ pullback.fst p.left x.left ≫ p.left ≫ Y.hom := by
        rw [p.w]
        simp only [Category.assoc]
      _ = a₀ ≫ s ≫ x.left ≫ Y.hom := by
        rw [← Category.assoc (pullback.fst p.left x.left), pullback.condition]
        simp only [s, Category.assoc]
      _ = b := by
        rw [← Category.assoc a₀, ha, Category.id_comp, x.w]
        rfl)
  refine ⟨a, ?_⟩
  apply Over.OverMorphism.ext
  change (a₀ ≫ pullback.fst p.left x.left) ≫ p.left = x.left
  rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Etale
