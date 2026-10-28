import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PointGroupDetection

/-! # Function Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.FunctionRigidity

noncomputable section

/-! Geometric point comparisons and actual function rigidity detect a
pointed morphism even when its source or base is nonreduced. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem overHom_fieldPoint_eq_of_baseChange
    {S : Scheme.{0}} {X Y : Over S} (f g : X ⟶ Y)
    {K : Type} [Field K] (s : Spec (.of K) ⟶ S)
    (h : (Over.pullback s).map f = (Over.pullback s).map g)
    (x : Over.mk s ⟶ X) : x ≫ f = x ≫ g := by
  let l : Spec (.of K) ⟶ pullback X.hom s :=
    pullback.lift x.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w x)
  have H := congrArg (fun z => l ≫ z.left ≫ pullback.fst Y.hom s) h
  apply Over.OverMorphism.ext
  change x.left ≫ f.left = x.left ≫ g.left
  simpa only [Over.pullback_map_left, ← Category.assoc, l, pullback.lift_fst] using H

theorem overHom_eq_one_of_geometricPoints
    {S : Scheme.{0}} (X Y : Over S) [GrpObj X] [GrpObj Y] [UniversallyClosed X.hom]
    (hΓ : ∀ V : S.Opens, IsIso (X.hom ∣_ V).appTop)
    (f : X ⟶ Y) (hzero : η[X] ≫ f = η[Y])
    (hfield : ∀ (K : Type) [Field K] [IsAlgClosed K]
      (s : Spec (.of K) ⟶ S) (x : Over.mk s ⟶ X), x ≫ f = 1) : f = 1 := by
  apply AbelianScheme.IsogenyQuotient.Field.PointGroupDetection.Construction.overHom_eq_one_of_fieldPoints X Y hΓ f hzero
  intro K _ s x
  let u := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have : Surjective u := ⟨Function.surjective_to_subsingleton _⟩
  have : Flat u := inferInstanceAs
    (Flat (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
  have : QuasiCompact u := inferInstanceAs
    (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
  have : Epi u := inferInstance
  let x' : Over.mk (u ≫ s) ⟶ X := Over.homMk (u ≫ x.left) (by
    rw [Category.assoc, x.w]
    rfl)
  have h := congrArg Over.Hom.left (hfield (AlgebraicClosure K) (u ≫ s) x')
  change (u ≫ x.left) ≫ f.left = (u ≫ s) ≫ η[Y].left at h
  apply Over.OverMorphism.ext
  change x.left ≫ f.left = s ≫ η[Y].left
  apply (cancel_epi u).mp
  simpa only [Category.assoc] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.FunctionRigidity
