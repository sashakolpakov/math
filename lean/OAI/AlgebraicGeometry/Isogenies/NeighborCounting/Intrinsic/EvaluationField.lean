import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationField
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ComponentLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange

/-! # Evaluation Field -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluationField.Lifts

noncomputable section

/-!
Construct a finite extension on which a native finite etale parameter
scheme is a disjoint union of rational points. This applies to the
generic torsion and neighbor parameter schemes before any reduction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ComponentLift.Components OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange

def affineAlgebraIso (R : Type u) [CommRing R]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) : EtaleTargetMaps.Components.affineOver R B ≅ EtaleTargetMaps.Components.affineOver R A :=
  (algSpec (.of R)).mapIso (CommAlgCat.isoMk e).op

def constantAffineIso (R : Type u) [CommRing R] (n : ℕ) :
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of R)) (ULift.{u} (Fin n)) ≅
      EtaleTargetMaps.Components.affineOver R (ULift.{u} (Fin n) → R) := by
  let e : (∐ fun _ : ULift.{u} (Fin n) => Spec (.of R)) ≅
      Spec (.of (ULift.{u} (Fin n) → R)) :=
    asIso (sigmaSpec (fun _ : ULift.{u} (Fin n) => CommRingCat.of R))
  refine Over.isoMk e ?_
  apply Sigma.hom_ext
  intro i
  change Sigma.ι _ i ≫ sigmaSpec (fun _ : ULift.{u} (Fin n) => CommRingCat.of R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (ULift.{u} (Fin n) → R))) =
      Sigma.ι _ i ≫ Sigma.desc (fun _ : ULift.{u} (Fin n) => 𝟙 (Spec (.of R)))
  rw [ι_sigmaSpec_assoc, Sigma.ι_comp_desc, ← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap R (ULift.{u} (Fin n) → R)) ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun _ : ULift.{u} (Fin n) => R) i) = 𝟙 _ := by
    ext r
    rfl
  rw [h, Spec.map_id]

/-- The native parameter scheme acquires individually evaluated points
over a constructed finite field extension. -/
theorem native_finite_evaluation_field (K : Type u) [Field K]
    (X : Over (Spec (.of K))) [IsFinite X.hom] [Etale X.hom] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L) (n : ℕ),
      Nonempty (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) (ULift.{u} (Fin n)) ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X) := by
  have hx : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨C, ⟨eC⟩⟩ := (essImage_algSpec (R := .of K) (G := X)).mpr hx
  change EtaleTargetMaps.Components.affineOver K C.unop ≅ X at eC
  have : Module.Finite K C.unop := ComponentLift.Components.finite_coordinates_of_iso K eC
  have : Algebra.Etale K C.unop := ComponentLift.Components.etale_coordinates_of_iso K eC
  obtain ⟨L, _, _, _, hsplit⟩ := EvaluationField.Lifts.exists_finite_evaluation_field K C.unop
  obtain ⟨n, ⟨e⟩⟩ := hsplit.nonempty_algEquiv_fun
  let e' : (L ⊗[K] C.unop) ≃ₐ[L] (ULift.{u} (Fin n) → L) :=
    e.trans (AlgEquiv.piCongrLeft' L (fun _ : Fin n => L) Equiv.ulift.symm)
  refine ⟨L, inferInstance, inferInstance, inferInstance, n, ⟨?_⟩⟩
  exact constantAffineIso L n ≪≫ affineAlgebraIso L e' ≪≫
    (AffineSpecialFiber.Components.affineBaseChangeIso K L C.unop).symm ≪≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso eC

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluationField.Lifts
