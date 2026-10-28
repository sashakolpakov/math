import OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalFieldUnramifiedReflection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedPullbackRefinements
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Unramified Fiber Stalk -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.UnramifiedFiberStalk.Geometric

noncomputable section

/-! The actual residue-field fiber detects formal unramifiedness of
the original stalk map. The proof compares actual iterated pullbacks
with the local-ring tensor product and uses finite relative differentials. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem unramified_pullback_precomp {X Y S T : Scheme.{u}}
    (f : X ⟶ S) (j : Y ⟶ X) [FormallyUnramified j] (b : T ⟶ S)
    [FormallyUnramified (pullback.snd f b)] : FormallyUnramified (pullback.snd (j ≫ f) b) := by
  let : FormallyUnramified (pullback.snd j (pullback.fst f b)) :=
    MorphismProperty.of_isPullback (P := @FormallyUnramified)
      (IsPullback.of_hasPullback j (pullback.fst f b)) inferInstance
  have h : FormallyUnramified ((pullbackRightPullbackFstIso f b j).inv ≫
      pullback.snd j (pullback.fst f b) ≫ pullback.snd f b) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance
      (MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance inferInstance)
  exact (congrArg FormallyUnramified (pullbackRightPullbackFstIso_inv_snd_snd f b j)).mp h

theorem formallyUnramified_stalkMap_of_residueBaseChange {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    [FormallyUnramified (pullback.snd f (X.fromSpecResidueField x ≫ f))] :
    (f.stalkMap x).hom.FormallyUnramified := by
  let R := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let K := X.residueField x
  let α : R ⟶ B := f.stalkMap x
  let : Algebra R B := α.hom.toAlgebra
  let : Algebra B K := (IsLocalRing.residue B).toAlgebra
  let : IsLocalHom (algebraMap B K) := inferInstanceAs (IsLocalHom (IsLocalRing.residue B))
  let : Algebra R K := ((IsLocalRing.residue B).comp α.hom).toAlgebra
  let : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.EssFiniteType R B := LocallyOfFiniteType.stalkMap f x
  let s := Y.fromSpecStalk (f x)
  let a := Spec.map α
  let c : Spec K ⟶ Spec R := Spec.map (α ≫ CommRingCat.ofHom (IsLocalRing.residue B))
  have hcs : c ≫ s = X.fromSpecResidueField x ≫ f := by
    let r : Spec K ⟶ Spec B := Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
    have hc' : c = r ≫ a := Spec.map_comp α (CommRingCat.ofHom (IsLocalRing.residue B))
    have hs' : a ≫ s = X.fromSpecStalk x ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
    calc
      c ≫ s = (r ≫ a) ≫ s := congrArg (fun k => k ≫ s) hc'
      _ = r ≫ (a ≫ s) := Category.assoc r a s
      _ = r ≫ (X.fromSpecStalk x ≫ f) := congrArg (fun k => r ≫ k) hs'
      _ = (r ≫ X.fromSpecStalk x) ≫ f := (Category.assoc r (X.fromSpecStalk x) f).symm
      _ = X.fromSpecResidueField x ≫ f := rfl
  let p := pullback.snd f s
  let q : Spec B ⟶ pullback f s :=
    pullback.lift (X.fromSpecStalk x) a (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm
  have hq : q ≫ pullback.fst f s = X.fromSpecStalk x := pullback.lift_fst _ _ _
  have hqp : q ≫ p = a := pullback.lift_snd _ _ _
  let : FormallyUnramified (q ≫ pullback.fst f s) := by rw [hq]; infer_instance
  let : FormallyUnramified q := FormallyUnramified.of_comp q (pullback.fst f s)
  let : FormallyUnramified (pullback.snd f (c ≫ s)) := by rw [hcs]; infer_instance
  let : FormallyUnramified (pullback.snd p c) := AbelianModuli.HilbertConstruction.UnramifiedPullbackRefinements.unramified_iterated_pullback f s c
  have hc : FormallyUnramified (pullback.snd (q ≫ p) c) := unramified_pullback_precomp p q c
  rw [hqp] at hc
  let : FormallyUnramified (pullback.snd a c) := hc
  let : Algebra K (B ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
  have ht : FormallyUnramified ((pullbackSpecIso R B K).inv ≫ pullback.snd a c) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance hc
  have hspec : FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap K (B ⊗[R] K)))) :=
    (pullbackSpecIso_inv_snd R B K) ▸ ht
  have halg : Algebra.FormallyUnramified K (B ⊗[R] K) :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp hspec
  exact LocalFieldUnramifiedReflection.Geometric.localAlgebra_formallyUnramified_of_rightLocalFieldFiber R B K halg

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.UnramifiedFiberStalk.Geometric
