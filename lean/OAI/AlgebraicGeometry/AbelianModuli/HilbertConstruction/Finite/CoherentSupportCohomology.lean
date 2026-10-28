import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.ClosedDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardCohomologyFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ZariskiVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Coherent Support Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoherentSupportCohomology

noncomputable section

/-! A coherent sheaf with finite support on a proper field scheme
descends to its actual finite annihilator subscheme. Consequently its
positive cohomology vanishes and its Euler characteristic is the
dimension of its actual global sections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem idealSubscheme_finite_of_finite_support
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (I : X.IdealSheafData) (hf : (I.support : Set X).Finite) :
    IsFinite (I.subschemeι ≫ p) := by
  let : Finite (I.support : Set X) := hf.to_subtype
  let j : I.subscheme → (I.support : Set X) := fun z =>
    ⟨I.subschemeι z, by rw [← I.range_subschemeι]; exact ⟨z, rfl⟩⟩
  let : Finite I.subscheme := Finite.of_injective j (fun a b h =>
    I.subschemeι.isEmbedding.injective (congrArg Subtype.val h))
  let : LocallyQuasiFinite (I.subschemeι ≫ p) :=
    LocallyQuasiFinite.of_finite_preimage_singleton (I.subschemeι ≫ p) (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite (I.subschemeι ≫ p)

theorem finiteSupport_coherent_positive_cohomology_isZero
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hf : ((Coherent.Annihilator.coherentAnnihilator M).support : Set X).Finite) (n : ℕ) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) (n + 1)).obj M) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let I := Coherent.Annihilator.coherentAnnihilator M
  let : IsFinite (I.subschemeι ≫ p) := idealSubscheme_finite_of_finite_support p I hf
  let : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ p)
  obtain ⟨N, hNq, hNt, ⟨e⟩⟩ := Coherent.ClosedDescent.exists_coherent_on_annihilating_subscheme M I le_rfl
  let := hNq
  let := hNt
  let H := Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) (n + 1)
  let eH := Affine.PushforwardCohomologyFiniteness.affinePushforwardCohomologyIso I.subschemeι p N (n + 1) ≪≫ H.mapIso e
  have : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H N (n + 1)) :=
    Affine.ZariskiVanishing.ZariskiCohomology.moduleAffineHSucc_subsingleton N n
  have hz : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (I.subschemeι ≫ p)) (n + 1)).obj N) :=
    Affine.ZariskiVanishing.ZariskiCohomology.moduleAffineHSucc_subsingleton N n
  exact eH.isZero_iff.mp (ModuleCat.isZero_of_subsingleton _)

theorem finiteSupport_coherent_euler_eq_sections
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hf : ((Coherent.Annihilator.coherentAnnihilator M).support : Set X).Finite) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M =
      (Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) : ℤ) :=
  CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing p M
    (finiteSupport_coherent_positive_cohomology_isZero p M hf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoherentSupportCohomology
