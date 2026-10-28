import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Characters
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SliceCharacters
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-! # Affine Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffinePullback.Construction

noncomputable section

/-!
# CartierDuality: affine coordinates for native scheme base change
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits _root_.Module TensorProduct
open scoped TensorProduct

universe u v

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [HopfAlgebra R A]

/-- The tensor-product coordinate algebra describes the native pullback
as a group scheme, with the group-law compatibility supplied by the
affine spectrum construction. -/
def affineHopfPullbackIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
      (Characters.Construction.affineHopfGroupScheme R A) ≅
        Characters.Construction.affineHopfGroupScheme S (S ⊗[R] A) := by
  let e := pullbackSymmetry .. ≪≫ pullbackSpecIso' R S A
  have h : IsMonHom (e.hom.asOver (Spec (CommRingCat.of S))) :=
    inferInstanceAs (IsMonHom
      ((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S A).hom.asOver (Spec (CommRingCat.of S))))
  let i : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
      (Characters.Construction.affineHopfGroupScheme R A)).X ≅ (Characters.Construction.affineHopfGroupScheme S (S ⊗[R] A)).X :=
    e.asOver (Spec (CommRingCat.of S))
  have : IsMonHom i.hom := h
  exact Grp.mkIso' i

/-- The affine pullback comparison preserves the projection to the
original affine group scheme. -/
theorem affineHopfPullbackIso_inv_fst :
    (affineHopfPullbackIso R S A).inv.hom.hom.left ≫
      Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) := by
  change (pullbackSpecIso' R S A).inv ≫ (Limits.pullbackSymmetry _ _).inv ≫
    Limits.pullback.fst _ _ = _
  rw [Limits.pullbackSymmetry_inv_comp_fst]
  exact pullbackSpecIso_inv_snd R S A

section MonoidAlgebra

variable (M : Type v) [CommMonoid M]

/-- Scalar extension of a monoid algebra respects comultiplication and
counit in addition to its algebra structure. -/
def monoidAlgebraBaseChangeBialgEquiv :
    S ⊗[R] MonoidAlgebra R M ≃ₐc[S] MonoidAlgebra S M where
  __ := (MonoidAlgebra.scalarTensorEquiv R S (M := M)).toLinearEquiv
  map_mul' := (MonoidAlgebra.scalarTensorEquiv R S (M := M)).map_mul
  counit_comp := by
    apply AlgebraTensorModule.ext
    intro s p
    induction p using MonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
    | single m r =>
      simp [MonoidAlgebra.scalarTensorEquiv_tmul, Algebra.smul_def, mul_comm]
  map_comp_comul := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add p q hp hq => simp only [map_add, hp, hq]
    | tmul s p =>
      induction p using MonoidAlgebra.induction_linear with
      | zero => simp
      | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
      | single m r =>
        simp [MonoidAlgebra.scalarTensorEquiv_tmul, Algebra.smul_def]

/-- The scalar-extension isomorphism identifies the old monoid algebra
with its ordinary coefficient-extension map. -/
theorem monoidAlgebraBaseChange_includeRight :
    ((monoidAlgebraBaseChangeBialgEquiv R S M).toAlgEquiv.toAlgHom.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : MonoidAlgebra R M →ₐ[R] S ⊗[R] MonoidAlgebra R M) =
    MonoidAlgebra.mapAlgHom M (Algebra.ofId R S) := by
  apply AlgHom.ext
  intro p
  change MonoidAlgebra.scalarTensorEquiv R S (1 ⊗ₜ[R] p) =
    MonoidAlgebra.mapAlgHom M (Algebra.ofId R S) p
  simp only [MonoidAlgebra.scalarTensorEquiv_tmul, one_smul]

end MonoidAlgebra

namespace Schemes

/-- On an affine scheme, the global multiplicative-group model agrees
with the Laurent-coordinate model used by the affine character theorem. -/
def multiplicativeGroupOverSpecIso (R : Type u) [CommRing R] :
    CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (CommRingCat.of R)) ≅ Characters.Construction.multiplicativeGroupScheme R := by
  letI : Algebra (ULift.{u} ℤ) R :=
    ((Int.castRingHom R).comp (ULift.ringEquiv.toRingHom)).toAlgebra
  have h : specULiftZIsTerminal.from (Spec (CommRingCat.of R)) =
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) R)) :=
    specULiftZIsTerminal.hom_ext _ _
  let i : Over.pullback (specULiftZIsTerminal.from (Spec (CommRingCat.of R))) ≅
      Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) R))) :=
    eqToIso (congrArg
      (fun g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) =>
        Over.pullback g) h)
  exact (Functor.mapGrpNatIso i).app (Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)) ≪≫
    affineHopfPullbackIso (ULift.{u} ℤ) R
      (Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ)) ≪≫
    ((hopfSpec (CommRingCat.of R)).mapIso
      (CommHopfAlgCat.isoMk
        (monoidAlgebraBaseChangeBialgEquiv (ULift.{u} ℤ) R (Multiplicative ℤ))).op).symm

/-- The global multiplicative-group model has the expected projection
to its integral Laurent-coordinate model. -/
theorem multiplicativeGroupOverSpecIso_inv_integralProjection (R : Type u) [CommRing R] :
    (multiplicativeGroupOverSpecIso R).inv.hom.hom.left ≫
      Limits.pullback.fst (Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)).X.hom
        (specULiftZIsTerminal.from (Spec (CommRingCat.of R))) =
      Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapRingHom (Multiplicative ℤ)
        ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom))) := by
  let : Algebra (ULift.{u} ℤ) R :=
    ((Int.castRingHom R).comp (ULift.ringEquiv.toRingHom)).toAlgebra
  let G₀ := Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)
  let f₀ := specULiftZIsTerminal.from (Spec (CommRingCat.of R))
  let f₁ := Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) R))
  have h : f₀ = f₁ := specULiftZIsTerminal.hom_ext _ _
  let i : Over.pullback f₀ ≅ Over.pullback f₁ :=
    eqToIso (congrArg (fun f : Spec (CommRingCat.of R) ⟶
      Spec (CommRingCat.of (ULift.{u} ℤ)) => Over.pullback f) h)
  let e := affineHopfPullbackIso (ULift.{u} ℤ) R
    (Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ))
  let j : (Over.pullback f₁).mapGrp.obj G₀ ≅ Characters.Construction.multiplicativeGroupScheme R :=
    e ≪≫ ((hopfSpec (CommRingCat.of R)).mapIso
      (CommHopfAlgCat.isoMk
        (monoidAlgebraBaseChangeBialgEquiv (ULift.{u} ℤ) R (Multiplicative ℤ))).op).symm
  have hstage : (multiplicativeGroupOverSpecIso R).inv.hom.hom.left ≫
      Limits.pullback.fst G₀.X.hom f₀ =
    j.inv.hom.hom.left ≫ Limits.pullback.fst G₀.X.hom f₁ := by
    change j.inv.hom.hom.left ≫ ((Functor.mapGrpNatIso i).inv.app G₀).hom.hom.left ≫
      Limits.pullback.fst G₀.X.hom f₀ = _
    exact congrArg (fun f => j.inv.hom.hom.left ≫ f) (SliceCharacters.Construction.Schemes.pullback_eqIso_inv_fst f₀ f₁ h G₀)
  apply hstage.trans
  change Spec.map (CommRingCat.ofHom
      (monoidAlgebraBaseChangeBialgEquiv (ULift.{u} ℤ) R (Multiplicative ℤ)).toAlgEquiv.toRingEquiv.toRingHom) ≫
        e.inv.hom.hom.left ≫ Limits.pullback.fst G₀.X.hom f₁ = _
  have hp := congrArg (fun f => Spec.map (CommRingCat.ofHom
      (monoidAlgebraBaseChangeBialgEquiv (ULift.{u} ℤ) R (Multiplicative ℤ)).toAlgEquiv.toRingEquiv.toRingHom) ≫ f)
    (affineHopfPullbackIso_inv_fst (ULift.{u} ℤ) R (Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ)))
  apply hp.trans
  have hs := congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom
      (monoidAlgebraBaseChange_includeRight (ULift.{u} ℤ) R (Multiplicative ℤ)))
  change Spec.map (CommRingCat.ofHom
    ((monoidAlgebraBaseChangeBialgEquiv (ULift.{u} ℤ) R (Multiplicative ℤ)).toAlgEquiv.toRingEquiv.toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom)) = _ at hs
  rw [CommRingCat.ofHom_comp, Spec.map_comp] at hs
  exact hs

end Schemes

/-- Affine-coordinate characters are exactly sections of the actual
fppf character sheaf on the corresponding affine test scheme. -/
def affineGroupCharacterSectionsEquiv :
    (Characters.Construction.affineHopfGroupScheme S (S ⊗[R] A) ⟶ Characters.Construction.multiplicativeGroupScheme S) ≃
      (CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)).obj.obj
        (Opposite.op ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))) :=
  (affineHopfPullbackIso R S A).homFromEquiv.symm.trans <|
    (Schemes.multiplicativeGroupOverSpecIso S).homToEquiv.symm.trans <|
      (SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv (Spec (CommRingCat.of R))
        (Characters.Construction.affineHopfGroupScheme R A)
        ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))).symm

variable [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A]

/-- The constructed affine Cartier dual represents sections of the actual
fppf character sheaf on every affine test scheme. Both sides use native
scheme morphisms and the global multiplicative-group model. -/
def affineCartierSheafSectionsEquiv :
    ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)) ⟶
      (Characters.Construction.affineHopfGroupScheme R (DualAlgebra.Construction.DualCoordinate R A)).X) ≃
    (CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)).obj.obj
      (Opposite.op ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))) :=
  (Characters.Construction.affineSchemePointsEquivAlgHom R (DualAlgebra.Construction.DualCoordinate R A) S).trans <|
    (DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).trans <|
      (Characters.Construction.groupLikeEquivSchemeCharacters S (S ⊗[R] A)).trans <|
        affineGroupCharacterSectionsEquiv R S A

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffinePullback.Construction
