import OAI.ArithmeticGeometry.Models.SpreadingOut.Projective
import OAI.ArithmeticGeometry.Models.SpreadingOut.Affine
import OAI.ArithmeticGeometry.Models.FoundationsPullback
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Projective Embedding -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.ProjectiveEmbedding.Construction

noncomputable section

/-! Affine finite-type schemes embed in standard affine charts of the
generic fibers of proper projective-space models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction

def projectiveModel (R : Type u) [CommRing R] (n : ℕ) : Over (Spec (.of R)) :=
  Over.mk (Projective.Construction.ProjectiveConstruction.projectiveSpaceToBase (K := R) n)

instance (R : Type u) [CommRing R] (n : ℕ) : IsProper (projectiveModel R n).hom :=
  Projective.Construction.ProjectiveConstruction.projectiveSpace_proper n

def projectiveChartHom (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    Affine.Construction.affineOver R (Projective.Construction.ProjectiveConstruction.projectiveChartPolynomial (K := R) n i) ⟶ projectiveModel R n :=
  Over.homMk (Projective.Construction.ProjectiveConstruction.projectiveAffineChartMap (K := R) n i)
    (Projective.Construction.ProjectiveConstruction.projectiveAffineChartMap_over n i)

instance (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    IsOpenImmersion (projectiveChartHom R n i).left :=
  inferInstanceAs (IsOpenImmersion (Projective.Construction.ProjectiveConstruction.projectiveAffineChartMap (K := R) n i))

def projectiveGenericChartIso
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ) (i : Fin (n + 1)) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (Affine.Construction.affineOver R (Projective.Construction.ProjectiveConstruction.projectiveChartPolynomial (K := R) n i)) ≅
      Affine.Construction.affineOver K (Projective.Construction.ProjectiveConstruction.projectiveChartPolynomial (K := K) n i) :=
  Affine.Construction.baseChangeAffineIso R K _ ≪≫ Affine.Construction.affineOverIso (MvPolynomial.algebraTensorAlgEquiv R K)

def projectiveGenericChartHom
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ) (i : Fin (n + 1)) :
    Affine.Construction.affineOver K (Projective.Construction.ProjectiveConstruction.projectiveChartPolynomial (K := K) n i) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (projectiveModel R n) :=
  (projectiveGenericChartIso R K n i).inv ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
      (projectiveChartHom R n i)

theorem projectiveGenericChartHom_openImmersion
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ) (i : Fin (n + 1)) :
    IsOpenImmersion (projectiveGenericChartHom R K n i).left := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let e := projectiveGenericChartIso R K n i
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have : IsOpenImmersion ((Over.pullback g).map (projectiveChartHom R n i)).left :=
    MorphismProperty.of_isPullback
      (FoundationsPullback.Constructions.pullback_over_map_isPullback g (projectiveChartHom R n i)).flip
      inferInstance
  change IsOpenImmersion (e.inv.left ≫ ((Over.pullback g).map (projectiveChartHom R n i)).left)
  infer_instance

theorem affine_finiteType_has_projective_chart_embedding
    (K A : Type u) [CommRing K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ (n : ℕ) (i : Affine.Construction.affineOver K A ⟶
        Affine.Construction.affineOver K (Projective.Construction.ProjectiveConstruction.projectiveChartPolynomial (K := K) n 0)),
      IsClosedImmersion i.left := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType K A)
  let e := MvPolynomial.renameEquiv K
    (Fintype.equivFinOfCardEq (Projective.Construction.ProjectiveConstruction.projectiveChartCoordinate_card n 0))
  let ψ := φ.comp e.toAlgHom
  have hψ : Function.Surjective ψ := hφ.comp e.surjective
  let j := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  let i : Affine.Construction.affineOver K A ⟶ Affine.Construction.affineOver K (Projective.Construction.ProjectiveConstruction.projectiveChartPolynomial (K := K) n 0) :=
    Over.homMk j (by
      change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K _)) =
          Spec.map (CommRingCat.ofHom (algebraMap K A))
      rw [← Spec.map_comp]
      exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) ψ.comp_algebraMap)
  exact ⟨n, i, IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom ψ.toRingHom) hψ⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.ProjectiveEmbedding.Construction
