import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LocalIsomorphismsIs
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationReduction
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Geometric Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricFiniteness

noncomputable section

/-!
# CartierDuality: detecting finiteness after algebraically closed base changes
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- A proper morphism over an arbitrary base is finite if every
base change to an algebraically closed field is finite. -/
theorem finite_of_algClosed_baseChanges {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [IsProper f.left]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S),
      IsFinite ((Over.pullback a).map f).left) : IsFinite f.left := by
  let : LocallyQuasiFinite f.left := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro y
    let K := AlgebraicClosure (Y.left.residueField y)
    let v : Spec (.of K) ⟶ Y.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
        Y.left.fromSpecResidueField y
    let a := v ≫ Y.hom
    let j : Spec (.of K) ⟶ pullback Y.hom a := pullback.lift v (𝟙 _) (by simp [a])
    let y' := j (IsLocalRing.closedPoint K)
    have hy : pullback.fst Y.hom a y' = y := by
      have hj : j ≫ pullback.fst Y.hom a = v := pullback.lift_fst _ _ _
      have hv : v (IsLocalRing.closedPoint K) = y := Y.left.fromSpecResidueField_apply y _
      exact (congrArg (fun g : Spec (.of K) ⟶ Y.left => g (IsLocalRing.closedPoint K)) hj).trans hv
    let fp := ((Over.pullback a).map f).left
    let : IsFinite fp := h K a
    have hf := (fp.finite_preimage_singleton y').image (pullback.fst X.hom a)
    rw [Scheme.image_preimage_eq_of_isPullback (LocalIsomorphismsIs.Construction.LocalIsomorphisms.pullbackMap_isPullback a f).flip,
      Set.image_singleton, hy] at hf
    exact hf
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

theorem finite_positive_powers_of_geometric_characteristic_primes {S : Scheme.{u}}
    (A : Over S) [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    (hchar : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
      (p : ℕ), p.Prime → (p : K) = 0 →
      let B := (Over.pullback a).obj A
      letI : GrpObj B := Functor.grpObjObj
      IsFinite ((𝟙 B : B ⟶ B) ^ p).left)
    (n : ℕ) (hn : 0 < n) : IsFinite ((𝟙 A : A ⟶ A) ^ n).left := by
  let : IsProper ((𝟙 A : A ⟶ A) ^ n).left := TorsionQuotient.Quasi.TorsionGeometry.power_isProper A n
  apply finite_of_algClosed_baseChanges
  intro K hK hclosed a
  let F := Over.pullback a
  let B := F.obj A
  let hgroup : GrpObj B := Functor.grpObjObj
  let hcomm : IsCommMonObj B := Functor.isCommMonObj_obj (F := F) (M := A)
  let hproper : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd A.hom a))
  have hf := @MultiplicationReduction.Construction.Multiplication.finite_positive_powers_of_characteristic_prime K hK B
    hgroup hcomm hproper (fun p hp hz => hchar K a p hp hz) n hn
  have he : F.map ((𝟙 A : A ⟶ A) ^ n) = (𝟙 B : B ⟶ B) ^ n :=
    ((F.homMonoidHom (X := A) (M := A)).map_pow (𝟙 A) n).trans
      (congrArg (fun f => f ^ n) (F.map_id A))
  exact (congrArg (fun f => f.left) he).symm ▸ hf

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricFiniteness
