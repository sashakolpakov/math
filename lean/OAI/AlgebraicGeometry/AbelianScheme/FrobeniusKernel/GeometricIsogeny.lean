import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogeny
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Geometric Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction

noncomputable section

/-!
Finite morphisms have finite geometric fibers, and finite surjective maps
lift every algebraically closed point. These are scheme-theoretic facts
used to apply the q-rank computation to the ordinary kernel operators.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

def geometricLiftSectionEquiv {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Spec (.of K) ⟶ Y) :
    {x : Spec (.of K) ⟶ X // x ≫ f = y} ≃
      {s : Spec (.of K) ⟶ pullback f y // s ≫ pullback.snd f y = 𝟙 _} where
  toFun x := ⟨pullback.lift x.val (𝟙 _) (x.property.trans (Category.id_comp y).symm),
    pullback.lift_snd _ _ _⟩
  invFun s := ⟨s.val ≫ pullback.fst f y, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, s.property, Category.id_comp]⟩
  left_inv x := Subtype.ext (pullback.lift_fst _ _ _)
  right_inv s := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans s.property.symm

omit [IsAlgClosed K] in
/-- A scheme finite over a field has finitely many underlying points. -/
theorem finite_points_over_field {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsFinite p] : Finite X := by
  have h := p.finite_preimage_singleton (IsLocalRing.closedPoint K)
  have he : p ⁻¹' {IsLocalRing.closedPoint K} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  exact Set.finite_univ_iff.mp ((congrArg Set.Finite he).mp h)

/-- The scheme-theoretic finite fiber gives a finite set of geometric
lifts, without requiring the fiber scheme to be reduced. -/
theorem finite_geometric_lifts {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (y : Spec (.of K) ⟶ Y) :
    Finite {x : Spec (.of K) ⟶ X // x ≫ f = y} := by
  let p := pullback.snd f y
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.snd f y))
  have : Finite ↥(pullback f y : Scheme.{u}) := finite_points_over_field p
  exact Finite.of_equiv (closedPoints (pullback f y : Scheme.{u}))
    ((geometricLiftSectionEquiv f y).trans (pointEquivClosedPoint p)).symm

/-- Surjective finite morphisms lift every algebraically closed point. -/
theorem exists_geometric_lift {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Surjective f] (y : Spec (.of K) ⟶ Y) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ f = y := by
  let p := pullback.snd f y
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.snd f y))
  have : Surjective p := inferInstanceAs (Surjective (pullback.snd f y))
  have : JacobsonSpace ↥(pullback f y : Scheme.{u}) := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨a, _⟩ := p.surjective (IsLocalRing.closedPoint K)
  obtain ⟨b, _, hb⟩ := nonempty_inter_closedPoints
    (Set.nonempty_of_mem (Set.mem_univ a)) isOpen_univ.isLocallyClosed
  let s := pointOfClosedPoint p b hb
  let x := (geometricLiftSectionEquiv f y).symm ⟨s, pointOfClosedPoint_comp p b hb⟩
  exact ⟨x.val, x.property⟩

def overGeometricFiberEquiv {S : Scheme.{u}} {A B : Over S}
    (f : A ⟶ B) (s : Spec (.of K) ⟶ S) (y : Over.mk s ⟶ B) :
    {x : Over.mk s ⟶ A // x ≫ f = y} ≃
      {x : Spec (.of K) ⟶ A.left // x ≫ f.left = y.left} where
  toFun x := ⟨x.val.left, congrArg (fun z => z.left) x.property⟩
  invFun x := ⟨Over.homMk x.val (by
    calc
      x.val ≫ A.hom = x.val ≫ f.left ≫ B.hom := congrArg (fun z => x.val ≫ z) f.w.symm
      _ = s := (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ B.hom) x.property).trans y.w)),
    Over.OverMorphism.ext x.property⟩
  left_inv x := by apply Subtype.ext; apply Over.OverMorphism.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

/-- An actual isogeny is surjective on geometric points. -/
theorem isogeny_geometricPoints_surjective {g h : ℕ} {S : Scheme.{u}}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (s : Spec (.of K) ⟶ S) :
    Function.Surjective (A.mapPoints B f.hom (Over.mk s)) := by
  intro y
  obtain ⟨x, hx⟩ := exists_geometric_lift f.hom.left y.left
  let z := (overGeometricFiberEquiv f.hom s y).symm ⟨x, hx⟩
  exact ⟨z.val, z.property⟩

/-- Its geometric kernel is finite even for inseparable isogenies. -/
theorem isogeny_geometricKernel_finite {g h : ℕ} {S : Scheme.{u}}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (s : Spec (.of K) ⟶ S) :
    Finite (f.kernelAt (Over.mk s)) := by
  have : Finite {x : Spec (.of K) ⟶ A.scheme.left //
      x ≫ f.hom.left = (1 : Over.mk s ⟶ B.scheme).left} :=
    finite_geometric_lifts f.hom.left (1 : Over.mk s ⟶ B.scheme).left
  exact Finite.of_equiv _ (overGeometricFiberEquiv f.hom s 1).symm

/-- Native abelian-scheme isogenies preserve q-rank when kernel points
have division lifts in the ordinary torsion tower. Finiteness and
surjectivity are proved from the isogeny, rather than postulated. -/
theorem isogeny_geometric_qRank_preserved {g h : ℕ} {S : Scheme.{u}}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (s : Spec (.of K) ⟶ S)
    (q : ℕ) (hdiv : ∀ k : f.kernelAt (Over.mk s),
      ∃ a : A.Points (Over.mk s), a ^ q = k.val) :
    Nat.card (A.torsionPoints q (Over.mk s)) =
      Nat.card (B.torsionPoints q (Over.mk s)) := by
  have : Finite (A.mapPoints B f.hom (Over.mk s)).ker := isogeny_geometricKernel_finite f s
  exact OrdinaryIsogeny.Construction.qTorsion_card_eq_of_kernel_divisible (A.mapPoints B f.hom (Over.mk s))
    (isogeny_geometricPoints_surjective f s) q hdiv

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction
