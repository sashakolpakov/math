import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionCokernelEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ExactPairs

/-! # Section Cokernel Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Cohomology and Euler formulas for the actual cokernel of a regular line-bundle map. Regularity is the explicit monomorphism hypothesis; no dimension or cohomological bound is assumed in the conclusion. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

namespace Regular.SectionCokernelCohomology.ZariskiCohomology

theorem coefficientCohomology_cokernel_isZero
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    {M Q : X.Modules} (f : M ⟶ Q) [Mono f] (n : ℕ)
    (hQ : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj Q))
    (hM : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj M)) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj (cokernel f)) := by
  let S : ShortComplex X.Modules :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact f⟩
  let π := ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).map (cokernel.π f)).hom
  let δ := (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS n).hom
  have hzQ : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj Q) :=
    ModuleCat.subsingleton_of_isZero hQ
  have hzM : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj M) :=
    ModuleCat.subsingleton_of_isZero hM
  have heq (x : (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj (cokernel f)) : x = 0 := by
    obtain ⟨y, hy⟩ := (CoefficientCohomology.ExactPairs.ZariskiCohomology.coefficientCohomology_exact_right c hS n x).mp (hzM.elim (δ x) 0)
    exact hy.symm.trans ((congrArg π (hzQ.elim y 0)).trans π.map_zero)
  have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj (cokernel f)) :=
    ⟨fun x y => (heq x).trans (heq y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

end Regular.SectionCokernelCohomology.ZariskiCohomology

theorem Regular.SectionCokernelCohomology.lineBundleMapCokernel_euler
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] {L M : Line.Bundles.LineBundle X}
    (f : L.sheaf ⟶ M.sheaf) [Mono f] :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (cokernel f) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M.sheaf - CohomologyEulerCharacteristic.coefficientEulerCharacteristic p L.sheaf := by
  have : L.sheaf.IsFiniteType := L.isFiniteType
  have : M.sheaf.IsFiniteType := M.isFiniteType
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  have : M.sheaf.IsQuasicoherent := M.isQuasicoherent
  have : (cokernel f).IsQuasicoherent := Quasicoherent.Cokernels.module_quasicoherent_cokernel f
  have : (cokernel f).IsFiniteType := Quasicoherent.QuotientFiniteType.quasicoherent_cokernel_finiteType f
  let S : ShortComplex X.Modules :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact f⟩
  have h := Proper.CohomologyEulerAdditivity.proper_coherent_euler_additive p hS
  change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M.sheaf =
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p L.sheaf + CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (cokernel f) at h
  omega

theorem Line.Bundles.LineBundle.tensor_succ_sheafIso {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) (m : ℕ) :
    Nonempty ((L.tensor (L.tensorPower m)).sheaf ≅ (L.tensorPower (m + 1)).sheaf) := by
  have h : Line.Bundles.LineBundle.classOf (L.tensor (L.tensorPower m)) =
      Line.Bundles.LineBundle.classOf (L.tensorPower (m + 1)) := by
    rw [Line.Bundles.LineBundle.classOf_tensor, Line.Bundles.LineBundle.classOf_tensorPower,
      Line.Bundles.LineBundle.classOf_tensorPower, pow_succ']
  exact Quotient.exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
