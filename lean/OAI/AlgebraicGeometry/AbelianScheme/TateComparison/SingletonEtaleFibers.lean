import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.SetTheory.Cardinal.Finite

/-! # Singleton Etale Fibers -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! A finite étale morphism with one lift of every geometric point is
an isomorphism. Extensionality on the étale target handles arbitrary test
schemes, including nonreduced ones. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem SingletonEtaleFibers.finiteEtale_isIso_of_singleton_geometric_fibers
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ Y),
      Nat.card {a : Spec (.of k) ⟶ X // a ≫ f = p} = 1) : IsIso f := by
  have : Etale (Over.mk f).hom := inferInstanceAs (Etale f)
  have hfmono : Mono f := by
    constructor
    intro T a b hab
    let Ta : Over Y := Over.mk (a ≫ f)
    let a' : Ta ⟶ Over.mk f := Over.homMk a rfl
    let b' : Ta ⟶ Over.mk f := Over.homMk b hab.symm
    have he : a' = b' := by
      apply IsogenyQuotient.Geometric.Points.Construction.etale_ext_of_geometric_points
      intro k _ _ p x
      have hc := (Nat.card_eq_one_iff_unique.mp (h k p)).1
      let l₁ : {a : Spec (.of k) ⟶ X // a ≫ f = p} :=
        ⟨(x ≫ a').left, (x ≫ a').w⟩
      let l₂ : {a : Spec (.of k) ⟶ X // a ≫ f = p} :=
        ⟨(x ≫ b').left, (x ≫ b').w⟩
      apply Over.OverMorphism.ext
      exact congrArg Subtype.val (hc.elim l₁ l₂)
    exact congrArg (fun g => g.left) he
  have hfsurj : Surjective f := by
    constructor
    intro y
    let k := AlgebraicClosure (Y.residueField y)
    let i := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k))
    let p := i ≫ Y.fromSpecResidueField y
    obtain ⟨a⟩ := (Nat.card_eq_one_iff_unique.mp (h k p)).2
    refine ⟨a.val (IsLocalRing.closedPoint k), ?_⟩
    change (a.val ≫ f) (IsLocalRing.closedPoint k) = y
    rw [a.property]
    exact Y.fromSpecResidueField_apply y (i (IsLocalRing.closedPoint k))
  exact Flat.isIso_of_surjective_of_mono f

variable {B : Scheme.{u}} {X : Over B} (C : Correspondences.EtaleCorrespondence X)
  {k : Type u} [Field k] (p : Spec (.of k) ⟶ X.left)

def Correspondences.EtaleCorrespondence.schemeSourceFiberEquiv :
    {a : Spec (.of k) ⟶ C.cover.left // a ≫ C.source.left = p} ≃
      C.Fiber (Over.homMk p rfl : Over.mk (p ≫ X.hom) ⟶ X) where
  toFun a := ⟨Over.homMk a.val (by
    rw [← C.source.w, ← Category.assoc, a.property]
    rfl), by
      apply Over.OverMorphism.ext
      exact a.property⟩
  invFun a := ⟨a.val.left, congrArg (fun g => g.left) a.property⟩
  left_inv _ := rfl
  right_inv a := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    rfl

theorem Correspondences.EtaleCorrespondence.source_isIso_of_fiber_card_one
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (b : Spec (.of k) ⟶ B) (x : Over.mk b ⟶ X), Nat.card (C.Fiber x) = 1) :
    IsIso C.source := by
  have : IsIso C.source.left := SingletonEtaleFibers.finiteEtale_isIso_of_singleton_geometric_fibers C.source.left
    (by
      intro k _ _ p
      rw [Nat.card_congr (C.schemeSourceFiberEquiv p)]
      exact h k (p ≫ X.hom) (Over.homMk p rfl))
  have : IsIso ((Over.forget B).map C.source) := inferInstanceAs (IsIso C.source.left)
  exact isIso_of_reflects_iso C.source (Over.forget B)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
