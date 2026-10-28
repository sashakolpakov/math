import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulCokernelEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.Annihilator

/-! # Mixed Koszul Cokernel Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulCokernelSupport

noncomputable section

/-! The actual mixed Koszul cokernel vanishes wherever one of its
sections is a frame. Its coherent annihilator is therefore supported
on the common zero set. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {X : Scheme.{u}}

theorem mixedKoszulCokernel_restrict_isZero
    (M : X.Modules) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (b : LineBundleKoszulComplex.LineBundleSection X) (hb : b ∈ bs) :
    IsZero ((MixedKoszulCokernelEuler.mixedKoszulCokernel M bs).restrict (Ample.LineBundles.sectionNonvanishing b.2).ι) := by
  let U := Ample.LineBundles.sectionNonvanishing b.2
  let R := Scheme.Modules.restrictFunctor U.ι
  let C := LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs
  have : PreservesLimits R := Module.RestrictionLimits.moduleRestrictFunctor_preservesLimits U.ι
  have : PreservesColimits R :=
    preservesColimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  have : R.Additive := Functor.additive_of_preserves_binary_products R
  let D := (R.mapHomologicalComplex (.up ℤ)).obj C
  have hs : IsIso ((Scheme.Modules.pullback U.ι).map b.2) :=
    (Section.Nonvanishing.isIso_pullbackSection_iff U.ι b.2).mp inferInstance
  have hc := LineBundleKoszulComplex.mixedLineBundleKoszulComplex_pullback_contractible M bs U.ι ⟨b, hb, hs⟩
  let e := (NatIso.mapHomologicalComplex (Scheme.Modules.restrictFunctorIsoPullback U.ι) (.up ℤ)).app C
  have hacy : D.Acyclic := Module.ComplexLocalExactness.cochain_acyclic_of_contractible D (MappingConeContractions.cochainContractible_of_iso e hc)
  have h₁ : IsZero (D.X 1) := R.map_isZero
    (LineBundleKoszulComplex.mixedLineBundleKoszulComplex_isZero_X M bs 1 (Or.inr (by omega)))
  let S := D.sc' (-1) 0 1
  have hexa : S.Exact :=
    ShortComplex.exact_of_iso (D.isoSc' (-1) 0 1 (by simp) (by simp)) (hacy 0)
  have : Epi (R.map (C.d (-1) 0)) :=
    (S.exact_iff_epi (h₁.eq_of_tgt _ _)).mp hexa
  exact (PreservesCokernel.iso R (C.d (-1) 0)).isZero_iff.mpr
    (isZero_cokernel_of_epi (R.map (C.d (-1) 0)))

theorem mixedKoszulCokernel_support_le
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (bs : List (LineBundleKoszulComplex.LineBundleSection X)) :
    letI := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M bs).1
    letI := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M bs).2
    ((Coherent.Annihilator.coherentAnnihilator (MixedKoszulCokernelEuler.mixedKoszulCokernel M bs)).support : Set X) ⊆ MixedKoszulGeometricSupport.mixedSectionZeroSet bs := by
  have := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M bs).1
  have := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M bs).2
  intro x hx b hb hxb
  have hn := (Coherent.Annihilator.coherentAnnihilator_mem_support_iff (MixedKoszulCokernelEuler.mixedKoszulCokernel M bs) x).mp hx
  exact hn ((Module.VanishingOpen.mem_moduleVanishingOpen (MixedKoszulCokernelEuler.mixedKoszulCokernel M bs) x).mpr
    ⟨Ample.LineBundles.sectionNonvanishing b.2, hxb, mixedKoszulCokernel_restrict_isZero M bs b hb⟩)

theorem mixedKoszulCokernel_support_finite
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (bs : List (LineBundleKoszulComplex.LineBundleSection X))
    (hf : (MixedKoszulGeometricSupport.mixedSectionZeroSet bs).Finite) :
    letI := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M bs).1
    letI := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M bs).2
    (((Coherent.Annihilator.coherentAnnihilator (MixedKoszulCokernelEuler.mixedKoszulCokernel M bs)).support : Set X)).Finite :=
  hf.subset (mixedKoszulCokernel_support_le M bs)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulCokernelSupport
