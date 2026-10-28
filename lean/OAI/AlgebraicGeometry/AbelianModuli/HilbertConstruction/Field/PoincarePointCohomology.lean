import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NontrivialPoincarePointCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfulFlatCohomologyVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldExtensionReflection
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Poincare Point Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Nonidentity rational dual points have zero Poincare-bundle cohomology over every field. The argument descends the algebraically closed result through actual scalar extension. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A)
variable (x : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme) (hx : x ≠ 1)

include hx in
theorem Dual.Data.DualAbelianData.poincarePointBundle_cohomology_vanish_overField (n : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (D.poincarePointBundle x).sheaf n) := by
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  let c := Spec.map φ
  have : Flat c := Smooth.FieldExtensionReflection.fieldSpecMap_flat φ
  have : Surjective c := Smooth.FieldExtensionReflection.fieldSpecMap_surjective φ
  have : A.scheme.left.IsSeparated := ⟨by rw [← terminal.comp_from A.scheme.hom]; infer_instance⟩
  have : CompactSpace A.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.scheme.hom
  have hx' : D.abelian.basePointPullback c x ≠ 1 :=
    D.abelian.basePointPullback_ne_one_of_flat_surjective c x hx
  have hzero := (D.pullback c).poincarePointBundle_cohomology_isZero
    (D.abelian.basePointPullback c x) hx' n
  have hp : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
      ((D.poincarePointBundle x).pullback (pullback.fst A.scheme.hom c)).sheaf n) :=
    AddCommGrpCat.subsingleton_of_isZero
      (((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (A.pullback c).scheme.left n).mapIso
        (D.poincarePointBundle_baseChangeIso c x)).isZero_iff.mp hzero)
  exact (FaithfulFlatCohomologyVanishing.fieldExtensionLineBundle_cohomology_vanish_iff
    (IsPullback.of_hasPullback A.scheme.hom c) (D.poincarePointBundle x) n).mp hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
