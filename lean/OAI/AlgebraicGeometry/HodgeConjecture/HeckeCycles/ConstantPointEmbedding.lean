import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantPointMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Constant Point Embedding -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantPointEmbedding.CM

noncomputable section

/-! Distinct field-valued points give a monomorphism from their constant
scheme. For finitely many points in a separated target, it is a closed
immersion. Nonempty test pieces map faithfully flatly to the base field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantPointMap.CM

universe u
variable (k : Type u) [Field k] (I : Type u) (A : Over (Spec (.of k)))
  (p : I → (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) (hp : Function.Injective p)

include hp in
theorem map_mono : Mono (ConstantPointMap.CM.ofPoints (Spec (.of k)) I A p) where
  right_cancellation {T} x y h := by
    apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of k)) I T).injective
    apply LocallyConstant.ext
    intro t
    let c : LocallyConstant T.left (I × I) := {
      toFun z := (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T x z, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T y z)
      isLocallyConstant := (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T x).isLocallyConstant.prodMk
        (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T y).isLocallyConstant }
    let U : Over (Spec (.of k)) := Over.mk ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c (c t)).ι ≫ T.hom)
    let d : U ⟶ T := Over.homMk (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c (c t)).ι rfl
    let b : U ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk U.hom (Category.comp_id U.hom)
    have hx (z : U.left) : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint U (d ≫ x) z = (c t).1 :=
      congrArg Prod.fst z.property
    have hy (z : U.left) : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint U (d ≫ y) z = (c t).2 :=
      congrArg Prod.snd z.property
    have hxp := ConstantPointMap.CM.ofPoints_on_constant (Spec (.of k)) I A p U (d ≫ x) (c t).1 hx
    have hyp := ConstantPointMap.CM.ofPoints_on_constant (Spec (.of k)) I A p U (d ≫ y) (c t).2 hy
    have hpoint : b ≫ p (c t).1 = b ≫ p (c t).2 :=
      hxp.symm.trans ((Category.assoc _ _ _).trans
        ((congrArg (d ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans hyp)))
    have : Surjective U.hom := ⟨fun z => ⟨⟨t, rfl⟩, Subsingleton.elim _ z⟩⟩
    have : Epi U.hom := Flat.epi_of_flat_of_surjective U.hom
    apply hp
    apply Over.OverMorphism.ext
    exact (cancel_epi U.hom).mp (congrArg (fun f : U ⟶ A => f.left) hpoint)

include hp in
theorem map_closed [Finite I] [IsSeparated A.hom] :
    IsClosedImmersion (ConstantPointMap.CM.ofPoints (Spec (.of k)) I A p).left := by
  let f := ConstantPointMap.CM.ofPoints (Spec (.of k)) I A p
  have : Mono f := map_mono k I A p hp
  have : IsFinite (f.left ≫ A.hom) :=
    (congrArg IsFinite f.w).mpr (AbelianModuli.HilbertConstruction.Finite.ConstantScheme.constantScheme_finite (S := Spec (.of k)) (I := I))
  have : IsFinite f.left := IsFinite.of_comp f.left A.hom
  exact (IsClosedImmersion.iff_isFinite_and_mono f.left).mpr ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantPointEmbedding.CM
