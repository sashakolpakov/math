import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Localization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Covers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationSpectrumIs

/-! # Principal Covers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PrincipalCovers.CrystallineFramePrincipalCovers

noncomputable section

/-!
# Native frame extensions preserve principal-open crystalline covers

Each localized frame map is the actual principal-open localization at
the original ambient coefficient. Thus the frame extension preserves
the constructed principal-open covers in the native crystalline topology,
including the affine translations between its chosen coordinate lifts.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a
local notation "G" => DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)

def map (s : Q.thickening.ring) : (F).obj (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s) ⟶ (F).obj Q :=
  (F).map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s)

theorem isLocalizationMap (s : Q.thickening.ring) :
    (Submonoid.powers (algebraMap Q.thickening.ring G s)).IsLocalizationMap (CrystallineFramePrincipalCovers.map p k B σ a Q s).ambientMap := by
  change (Submonoid.powers (algebraMap Q.thickening.ring G s)).IsLocalizationMap
    (Map.CrystallineFrameMap.ambientMap a (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s))
  have hf : (Submonoid.powers s).IsLocalizationMap
      (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s).ambientMap := by
    change (Submonoid.powers s).IsLocalizationMap (algebraMap Q.thickening.ring (Localization.Away s))
    exact (inferInstance : IsLocalization (Submonoid.powers s) (Localization.Away s)).toIsLocalizationMap
  have hd := CrystallineFrame.Localization.CrystallineFrameLocalization.ambientMap_isLocalization p k B σ a
    (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s) (Submonoid.powers s) hf
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using hd

theorem ambient_openImmersion (s : Q.thickening.ring) :
    IsOpenImmersion ((Site.ambient p k X).map (CrystallineFramePrincipalCovers.map p k B σ a Q s)) :=
  LocalizationSpectrumIs.LocalizationSpectrum.isOpenImmersion G _ (CrystallineFramePrincipalCovers.map p k B σ a Q s).ambientMap.toRingHom
    (algebraMap Q.thickening.ring G s) (isLocalizationMap p k B σ a Q s)

theorem ambient_range (s : Q.thickening.ring) :
    Set.range (((Site.ambient p k X).map (CrystallineFramePrincipalCovers.map p k B σ a Q s)) :
      ((Site.ambient p k X).obj ((F).obj (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q s))) →
        ((Site.ambient p k X).obj ((F).obj Q))) =
      (PrimeSpectrum.basicOpen (algebraMap Q.thickening.ring G s) : Set (PrimeSpectrum G)) :=
  LocalizationSpectrumIs.LocalizationSpectrum.range G _ (CrystallineFramePrincipalCovers.map p k B σ a Q s).ambientMap.toRingHom
    (algebraMap Q.thickening.ring G s) (isLocalizationMap p k B σ a Q s)

theorem covering_mem (ι : Type u) (s : ι → Q.thickening.ring) (hs : Ideal.span (Set.range s) = ⊤) :
    Sieve.generate ((CrystallinePrincipal.Covers.CrystallinePrincipalCovers.presieve p k X Q ι s).map F) ∈
      Site.topology p k X ((F).obj Q) := by
  apply Site.covering_mem
  rw [CrystallinePrincipal.Covers.CrystallinePrincipalCovers.presieve, Presieve.map_ofArrows, Presieve.map_ofArrows,
    Scheme.ofArrows_mem_precoverage_iff]
  constructor
  · intro x
    obtain ⟨i, hi⟩ := CrystallinePrincipal.Covers.CrystallinePrincipalCovers.exists_basicOpen p k X Q ι s hs
      (PrimeSpectrum.comap (algebraMap Q.thickening.ring G) x)
    refine ⟨i, ?_⟩
    have hxi : (x : PrimeSpectrum G) ∈
        (PrimeSpectrum.basicOpen (algebraMap Q.thickening.ring G (s i)) : Set (PrimeSpectrum G)) := hi
    exact (ambient_range p k B σ a Q (s i)).symm ▸ hxi
  · intro i
    exact ambient_openImmersion p k B σ a Q (s i)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PrincipalCovers.CrystallineFramePrincipalCovers
